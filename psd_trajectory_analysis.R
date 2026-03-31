# =============================================================================
# psd_trajectory_analysis.R
#
# Trajectory Classes of Post-Stroke Depression Severity and Their Baseline
# Predictors: A Multi-Cohort Replication Study
#
# Authors: Lena Oestreich et al.
# Journal: Journal of Affective Disorders (under review)
#
# Description:
#   Latent Class Growth Analysis (LCGA) of post-stroke depression severity
#   across three independent cohorts, followed by BCH-corrected regression
#   to identify baseline predictors of trajectory class membership.
#
# Cohorts:
#   PSS     — Bulgarian Post-Stroke Study         (n=85;  GDS-15)
#   EpiUSA  — Epidemiologic Study of Risk of      (n=473; HAMD-17)
#             Dementia After Stroke
#   SSS     — Sydney Stroke Study                 (n=192; GDS-15 and HAMD-17)
#
# Analyses:
#   1.  PSS     — GDS    (within-cohort)
#   2.  EpiUSA  — HAMD   (within-cohort)
#   3.  SSS     — GDS    (within-cohort)
#   4.  SSS     — HAMD   (within-cohort)
#   5.  Pooled  — HAMD   (EpiUSA + SSS; primary pooled analysis)
#   6.  Pooled  — GDS    (PSS + SSS; secondary pooled analysis)
#
# Model selection strategy (per analysis):
#   Step 1: Compare functional forms (linear, quadratic, natural cubic spline)
#           using 1-class LGC models; select by lowest BIC.
#   Step 2: LCGA class enumeration (2–4 classes) using winning functional form;
#           select by BIC, entropy (>0.80), and class size (no class < 5%).
#
# All models estimated via full information maximum likelihood (FIML) in lcmm.
# Pooled analyses use within-cohort T-score standardisation (mean=50, SD=10).
#
# BCH regression:
#   Primary:   Pooled HAMD (EpiUSA + SSS; n=665)
#   Secondary: Pooled GDS  (PSS + SSS;    n=277)
#   Predictors: age, sex (female), hypertension, diabetes, global cognition (z)
#   Covariate:  cohort (EpiUSA vs SSS / PSS vs SSS)
#   Reference:  Class 1 (No Depression)
#
# Dependencies:
#   lcmm, dplyr, tidyr, ggplot2, splines, tableone, nnet, broom
#
# Input files (place in data/ subdirectory):
#   dataset_PSS_GDS.csv
#   dataset_EpiUSA_HAMD.csv
#   dataset_SSS.csv
#   dataset_pooled_HAMD.csv   (long format; includes time_yrs, HAMD, HAMD_T)
#   dataset_pooled_GDS.csv    (long format; includes time_yrs, GDS_T)
#   master_PSD_dataset.csv    (merged baseline variables, all cohorts)
#
# Output files (written to output/ subdirectory):
#   table1_baseline.csv
#   class_assignments_<cohort>.csv  (one per analysis)
#   bch_results_pooled_HAMD.csv
#   bch_results_pooled_GDS.csv
#   plot_assessment_counts.png
#   plot_PSS_GDS.png
#   plot_EpiUSA_HAMD.png
#   plot_SSS_GDS.png
#   plot_SSS_HAMD.png
#   plot_Pooled_HAMD.png
#   plot_Pooled_GDS.png
# =============================================================================


# =============================================================================
# 0.  SETUP
# =============================================================================

library(lcmm)      # LCGA / LGC models (Proust-Lima et al.)
library(dplyr)
library(tidyr)
library(ggplot2)
library(splines)   # ns() for natural cubic splines
library(tableone)  # CreateTableOne
library(nnet)      # multinom (not used directly but loaded for BCH context)
library(broom)     # tidy() for model output

# ── Paths ─────────────────────────────────────────────────────────────────────
# Set DATA_DIR to the folder containing your input CSV files.
# Set OUT_DIR  to the folder where outputs should be written.
# Both directories must exist before running.

DATA_DIR <- "data"    # e.g. "data" or "/path/to/your/data"
OUT_DIR  <- "output"  # e.g. "output" or "/path/to/your/output"

data_path <- function(f) file.path(DATA_DIR, f)
out_path  <- function(f) file.path(OUT_DIR,  f)

# ── Helper: print model comparison table ──────────────────────────────────────
summarise_models <- function(model_list, label) {
  cat("\n══════════════════════════════════════════\n")
  cat(" ", label, "\n")
  cat("══════════════════════════════════════════\n")
  res <- lapply(model_list, function(m) {
    data.frame(
      classes = m$ng,
      loglik  = round(m$loglik, 2),
      AIC     = round(m$AIC,    2),
      BIC     = round(m$BIC,    2),
      entropy = ifelse(m$ng > 1, round(m$entropy, 3), NA),
      conv    = m$conv
    )
  })
  print(do.call(rbind, res), row.names = FALSE)
}

# ── Helper: reshape wide → long for lcmm ──────────────────────────────────────
# Two calling modes:
#   (a) score_cols / yrs_cols supplied explicitly  — use for PSS (irregular names)
#   (b) score_prefix / yrs_prefix                  — auto-detects columns matching
#       ^<prefix>_t[0-9]+$ and ^<prefix>_t[0-9]+_yrs$, sorted by index
#
# The function returns one row per observed timepoint (NA rows are dropped so
# FIML in lcmm operates on all available observations).

to_long_lcmm <- function(df,
                          score_prefix = NULL, yrs_prefix = NULL,
                          score_cols   = NULL, yrs_cols   = NULL,
                          id_col       = "patient_id") {

  if (is.null(score_cols)) {
    score_cols <- grep(paste0("^", score_prefix, "_t[0-9]+$"),
                       names(df), value = TRUE)
    yrs_cols   <- grep(paste0("^", yrs_prefix,   "_t[0-9]+_yrs$"),
                       names(df), value = TRUE)
    # Ensure chronological order
    score_cols <- score_cols[order(as.integer(sub(".*_t([0-9]+)$",     "\\1", score_cols)))]
    yrs_cols   <- yrs_cols[order(  as.integer(sub(".*_t([0-9]+)_yrs$", "\\1", yrs_cols)))]
  }
  stopifnot(length(score_cols) == length(yrs_cols))

  demo_cols <- setdiff(names(df), c(score_cols, yrs_cols))

  long <- lapply(seq_along(score_cols), function(i) {
    tmp <- df[, c(demo_cols, score_cols[i], yrs_cols[i])]
    names(tmp)[names(tmp) == score_cols[i]] <- "score"
    names(tmp)[names(tmp) == yrs_cols[i]]   <- "time"
    tmp$obs <- i
    tmp
  })

  out <- bind_rows(long)
  out <- out[!is.na(out$score), ]                              # drop unobserved rows
  out[[id_col]] <- as.integer(factor(out[[id_col]]))           # integer ID required by lcmm
  out
}

# ── Shared ggplot theme for trajectory plots ───────────────────────────────────
traj_theme <- theme_bw(base_size = 25) +
  theme(
    legend.position    = "bottom",
    legend.box.spacing = unit(2, "pt"),
    panel.grid.major   = element_blank(),
    panel.grid.minor   = element_blank()
  )

# ── Trajectory class colours (consistent across all plots) ───────────────────
CLASS_COLS <- c(amber = "#F0B429", blue = "#2E86C1", red = "#C41E3A")


# =============================================================================
# 1.  LOAD DATA
# =============================================================================

pss        <- read.csv(data_path("dataset_PSS_GDS.csv"),        stringsAsFactors = FALSE)
epi        <- read.csv(data_path("dataset_EpiUSA_HAMD.csv"),    stringsAsFactors = FALSE)
sss        <- read.csv(data_path("dataset_SSS.csv"),            stringsAsFactors = FALSE)
pooled     <- read.csv(data_path("dataset_pooled_HAMD.csv"),    stringsAsFactors = FALSE)
pooled_gds <- read.csv(data_path("dataset_pooled_GDS.csv"),     stringsAsFactors = FALSE)
master     <- read.csv(data_path("master_PSD_dataset.csv"),     stringsAsFactors = FALSE)

# Create integer IDs required by lcmm (replaces original string patient_id)
pss$id_int        <- as.integer(factor(pss$patient_id))
epi$id_int        <- as.integer(factor(epi$patient_id))
sss$id_int        <- as.integer(factor(sss$patient_id))
pooled$id_int     <- as.integer(factor(pooled$patient_id))
pooled_gds$id_int <- as.integer(factor(pooled_gds$patient_id))

cat("Enrolled sample sizes:\n")
cat("  PSS n    =", nrow(pss),    "\n")
cat("  EpiUSA n =", nrow(epi),    "\n")
cat("  SSS n    =", nrow(sss),    "\n")


# =============================================================================
# 2.  SAMPLE DESCRIPTION (Table 1)
# =============================================================================

# ── Recode master dataset variables ───────────────────────────────────────────

master$depress_prior[master$depress_prior == 9] <- NA
master$depress_prior <- factor(master$depress_prior, levels = c(0, 1),
                                labels = c("No", "Yes"))

master$stroke_prior[master$stroke_prior == "no"]  <- 0
master$stroke_prior[master$stroke_prior == "yes"] <- 1
master$stroke_prior <- suppressWarnings(as.numeric(master$stroke_prior))
master$stroke_prior[master$study == "PSS"] <- NA   # not collected in PSS
master$stroke_prior <- factor(master$stroke_prior, levels = c(0, 1),
                               labels = c("No", "Yes"))

master$stroketype[master$stroketype %in% c("1", "1.0", "ischaemic stroke")] <- "Ischaemic"
master$stroketype[master$stroketype == "3"]   <- "Haemorrhagic"
master$stroketype[master$stroketype == "TIA"] <- "TIA"
master$stroketype[master$stroketype == ""]    <- NA
master$stroketype <- factor(master$stroketype)

master$sex[master$sex == ""] <- NA
master$sex <- factor(master$sex)

for (v in c("hypertension", "diabetes", "MI", "AF", "smoking_ever")) {
  master[[v]] <- factor(master[[v]])
}

# ── Restrict to analytic sample ───────────────────────────────────────────────
# Analytic IDs are populated after running the LCGA sections below.
# Update the vectors below with the patient_id values of the analytic sample.
# Example:
#   pss_analytic_ids    <- unique(pss_long$patient_id)
#   epi_analytic_ids    <- unique(epi_long$patient_id)
#   sss_analytic_ids    <- unique(c(sss_gds_long$patient_id,
#                                   sss_hamd_long$patient_id))
analytic_ids <- c(
  as.character(pss_analytic_ids),
  as.character(epi_analytic_ids),
  as.character(sss_analytic_ids)
)
ma <- master[master$patient_id %in% analytic_ids, ]
cat("\nAnalytic n:", nrow(ma), "\n")
print(table(ma$study))

# ── Create and export Table 1 ─────────────────────────────────────────────────
vars    <- c("age", "sex", "eduyrs", "hypertension", "diabetes", "MI", "AF",
             "smoking_ever", "stroke_prior", "depress_prior", "stroketype")
catvars <- c("sex", "hypertension", "diabetes", "MI", "AF",
             "smoking_ever", "stroke_prior", "depress_prior", "stroketype")

tab1 <- CreateTableOne(vars      = vars,
                        strata    = "study",
                        data      = ma,
                        factorVars = catvars,
                        addOverall = TRUE)

out_tab1 <- print(tab1, showAllLevels = FALSE, quote = FALSE,
                   noSpaces = TRUE, printToggle = FALSE)
write.csv(out_tab1, out_path("table1_baseline.csv"))
cat("Table 1 saved.\n")


# =============================================================================
# 3.  ASSESSMENT COUNT PLOT (Figure 1)
# =============================================================================
# Built from the long-format data objects created in Sections 4–7 below.
# Run this block after Sections 4–7.

pss_counts <- pss_long %>%
  group_by(time) %>%
  summarise(n = sum(!is.na(score)), .groups = "drop") %>%
  mutate(cohort = "PSS (GDS-15)")

epi_counts <- epi_long %>%
  group_by(time) %>%
  summarise(n = sum(!is.na(score)), .groups = "drop") %>%
  mutate(cohort = "EpiUSA (HAMD-17)")

sss_gds_counts <- sss_gds_long %>%
  group_by(time) %>%
  summarise(n = sum(!is.na(score)), .groups = "drop") %>%
  mutate(cohort = "SSS (GDS-15)")

sss_hamd_counts <- sss_hamd_long %>%
  group_by(time) %>%
  summarise(n = sum(!is.na(score)), .groups = "drop") %>%
  mutate(cohort = "SSS (HAMD-17)")

counts_df <- bind_rows(pss_counts, epi_counts, sss_gds_counts, sss_hamd_counts)

plot_counts <- ggplot(counts_df, aes(x = time, y = n, colour = cohort)) +
  geom_line(linewidth = 1.0) +
  geom_point(size = 4, shape = 16) +
  scale_x_continuous(
    trans  = "sqrt",
    breaks = c(0.015, 0.0833, 0.25, 0.5, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10),
    labels = c("5d", "1mo", "3mo", "6mo", "1yr", "2yr", "3yr",
               "4yr", "5yr", "6yr", "7yr", "8yr", "9yr", "10yr"),
    guide  = guide_axis(angle = 45)
  ) +
  scale_y_continuous(limits = c(0, 450), breaks = seq(0, 450, 50)) +
  scale_colour_manual(values = c(
    "PSS (GDS-15)"     = "#A85C6B",
    "EpiUSA (HAMD-17)" = "#3D7EAA",
    "SSS (GDS-15)"     = "#C4954A",
    "SSS (HAMD-17)"    = "#5A8A6A"
  )) +
  labs(x = "Time post-stroke", y = "Number of participants",
       title = "Number of depression severity assessments",
       colour = NULL) +
  guides(colour = guide_legend(nrow = 2)) +
  traj_theme +
  theme(legend.margin = margin(t = -10))

ggsave(out_path("plot_assessment_counts.png"), plot_counts,
       width = 11, height = 7, dpi = 300)
cat("Assessment counts plot saved.\n")


# =============================================================================
# 4.  PSS — GDS  (n=85)
#
# Timepoints (supplied explicitly due to non-numeric 1-month label):
#   t0     = 5 days    (0.0137 yrs)  n=85
#   t_1mo  = 1 month   (0.0833 yrs)  n=83
#   t1     = 6 months  (0.5 yrs)     n=78
#   t2     = 12 months (1.0 yrs)     n=73
#   t3     = 24 months (2.0 yrs)     n=21  — sparse; retained under FIML
#
# GDS-15 severity thresholds: no depression 0–4, mild 5–8,
#                              moderate 9–11, severe ≥12
# =============================================================================

cat("\n────────────────────────────────────────────────────────\n")
cat(" 4. PSS — GDS\n")
cat("────────────────────────────────────────────────────────\n")

pss_score_cols <- c("GDS_t0", "GDS_t_1mo", "GDS_t1", "GDS_t2", "GDS_t3")
pss_yrs_cols   <- c("GDS_t0_yrs", "GDS_t_1mo_yrs", "GDS_t1_yrs",
                    "GDS_t2_yrs", "GDS_t3_yrs")

pss_long <- to_long_lcmm(pss,
                          score_cols = pss_score_cols,
                          yrs_cols   = pss_yrs_cols,
                          id_col     = "patient_id")
pss_long$id_int <- as.integer(factor(pss_long$patient_id))

cat("PSS long: n_obs =", nrow(pss_long),
    " | n_patients =", n_distinct(pss_long$patient_id), "\n")

# ── Step 1: Functional form selection (1-class LGC) ───────────────────────────
pss_lgc_lin <- hlme(score ~ time,
                    subject = "id_int", ng = 1,
                    data = pss_long, verbose = FALSE)

pss_lgc_quad <- hlme(score ~ time + I(time^2),
                     subject = "id_int", ng = 1,
                     data = pss_long, verbose = FALSE)

# Spline knots at 1 month (0.0833) and 6 months (0.5):
#   captures acute-phase change and sub-acute to chronic transition.
#   Boundary knots implicitly at 5-day (min) and 24-month (max).
pss_lgc_spline <- hlme(score ~ ns(time, knots = c(1/12, 0.5)),
                       subject = "id_int", ng = 1,
                       data = pss_long, verbose = FALSE)

cat("\nPSS LGC functional form comparison:\n")
summarytable(pss_lgc_lin, pss_lgc_quad, pss_lgc_spline,
             which = c("G", "loglik", "AIC", "BIC", "conv"))

# Selected form: linear (lowest BIC)
best_pss_lgc <- pss_lgc_lin

# ── Step 2: Class enumeration (2–4 classes) ───────────────────────────────────
# PSS n=85; 4-class solution should be interpreted cautiously.
# Any class <5% of sample (~4 patients) is flagged as unreliable.

pss_fixed   <- score ~ time
pss_mixture <- ~ time

set.seed(42)
pss_lcga_2 <- gridsearch(
  hlme(pss_fixed, mixture = pss_mixture,
       subject = "id_int", ng = 2, data = pss_long, verbose = FALSE),
  rep = 30, maxiter = 30, minit = best_pss_lgc
)
set.seed(42)
pss_lcga_3 <- gridsearch(
  hlme(pss_fixed, mixture = pss_mixture,
       subject = "id_int", ng = 3, data = pss_long, verbose = FALSE),
  rep = 30, maxiter = 30, minit = best_pss_lgc
)
set.seed(42)
pss_lcga_4 <- gridsearch(
  hlme(pss_fixed, mixture = pss_mixture,
       subject = "id_int", ng = 4, data = pss_long, verbose = FALSE),
  rep = 30, maxiter = 30, minit = best_pss_lgc
)

cat("\nPSS LCGA class enumeration:\n")
summarytable(best_pss_lgc, pss_lcga_2, pss_lcga_3, pss_lcga_4,
             which = c("G", "loglik", "AIC", "BIC", "entropy", "conv"))

for (m in list(pss_lcga_2, pss_lcga_3, pss_lcga_4)) {
  cat("\nPSS class sizes (ng =", m$ng, "):\n")
  pct <- round(table(m$pprob$class) / nrow(m$pprob) * 100, 1)
  print(pct)
  if (any(pct < 5)) cat("  *** WARNING: class below 5% — consider fewer classes ***\n")
}

# ── Selected model: 3-class linear ────────────────────────────────────────────
# Classes: No Depression (58%), Mild Stable (29%), Moderate Worsening (13%)

pss_lcga_3_final <- hlme(score ~ time, mixture = ~ time,
                         subject = "id_int", ng = 3,
                         data = pss_long, verbose = FALSE,
                         B = pss_lcga_3$best)

# ── Trajectory plot ───────────────────────────────────────────────────────────
timeseq_pss <- data.frame(time = seq(0, 2, by = 0.02))
pred_pss    <- predictY(pss_lcga_3_final, newdata = timeseq_pss,
                        var.time = "time", draws = TRUE)

pred_pss_df <- data.frame(
  time  = rep(timeseq_pss$time, 3),
  score = c(pred_pss$pred[, "Ypred_class1"],
            pred_pss$pred[, "Ypred_class2"],
            pred_pss$pred[, "Ypred_class3"]),
  lower = c(pred_pss$pred[, "lower.Ypred_class1"],
            pred_pss$pred[, "lower.Ypred_class2"],
            pred_pss$pred[, "lower.Ypred_class3"]),
  upper = c(pred_pss$pred[, "upper.Ypred_class1"],
            pred_pss$pred[, "upper.Ypred_class2"],
            pred_pss$pred[, "upper.Ypred_class3"]),
  class = factor(
    rep(c("Class 3: Moderate worsening (13%)",
          "Class 2: Mild stable (29%)",
          "Class 1: No depression (58%)"),
        each = nrow(timeseq_pss)),
    levels = c("Class 1: No depression (58%)",
               "Class 2: Mild stable (29%)",
               "Class 3: Moderate worsening (13%)")
  )
)

plot_pss <- ggplot(pred_pss_df, aes(x = time, y = score,
                                    colour = class, fill = class)) +
  geom_ribbon(aes(ymin = lower, ymax = upper), alpha = 0.2, colour = NA) +
  geom_line(linewidth = 1.1) +
  geom_hline(yintercept = c(5, 9, 12), linetype = "dotted", colour = "grey70") +
  annotate("text", x = 2, y = c(0,    5.7,  9.7,  12.7),
           label = c("No Depression (0-4)", "Mild (5-8)", "Moderate (9-11)", "Severe (\u226512)"),
           hjust = 1, size = 7, colour = "grey35") +
  scale_x_continuous(breaks = c(0, 1/12, 0.5, 1, 2),
                     labels = c("5d", "1mo", "6mo", "1yr", "2yr"),
                     guide  = guide_axis(angle = 45)) +
  scale_y_continuous(breaks = seq(0, 15, 3)) +
  scale_colour_manual(values = c(
    "Class 1: No depression (58%)"      = CLASS_COLS["amber"],
    "Class 2: Mild stable (29%)"        = CLASS_COLS["blue"],
    "Class 3: Moderate worsening (13%)" = CLASS_COLS["red"]
  )) +
  scale_fill_manual(values = c(
    "Class 1: No depression (58%)"      = CLASS_COLS["amber"],
    "Class 2: Mild stable (29%)"        = CLASS_COLS["blue"],
    "Class 3: Moderate worsening (13%)" = CLASS_COLS["red"]
  )) +
  labs(x = "Time post-stroke", y = "GDS-15 score",
       title = "PSS GDS: 3-class LCGA",
       colour = NULL, fill = NULL) +
  guides(colour = guide_legend(nrow = 2), fill = guide_legend(nrow = 2)) +
  traj_theme

ggsave(out_path("plot_PSS_GDS.png"), plot_pss, width = 10, height = 7, dpi = 300)
cat("PSS plot saved.\n")


# =============================================================================
# 5.  EpiUSA — HAMD  (n=473)
#
# Timepoints: t1=3mo, t2=1yr, t3=2yr, ..., t11=10yr  (11 waves)
# Time in years: 0.25, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10
#
# HAMD-17 severity thresholds: no depression 0–7, mild 8–13,
#                              moderate 14–18, severe 19–22, very severe ≥23
# =============================================================================

cat("\n────────────────────────────────────────────────────────\n")
cat(" 5. EpiUSA — HAMD\n")
cat("────────────────────────────────────────────────────────\n")

epi_long <- to_long_lcmm(epi, score_prefix = "HAMD", yrs_prefix = "HAMD",
                          id_col = "patient_id")
epi_long$id_int <- as.integer(factor(epi_long$patient_id))

cat("EpiUSA long: n_obs =", nrow(epi_long),
    " | n_patients =", n_distinct(epi_long$patient_id), "\n")

# ── Step 1: Functional form ────────────────────────────────────────────────────
epi_lgc_lin <- hlme(score ~ time,
                    subject = "id_int", ng = 1,
                    data = epi_long, verbose = FALSE)

epi_lgc_quad <- hlme(score ~ time + I(time^2),
                     subject = "id_int", ng = 1,
                     data = epi_long, verbose = FALSE)

# Spline knots at 1, 3, 7 years — roughly evenly spaced on log-time scale
epi_lgc_spline <- hlme(score ~ ns(time, knots = c(1, 3, 7)),
                       subject = "id_int", ng = 1,
                       data = epi_long, verbose = FALSE)

cat("\nEpiUSA LGC functional form comparison:\n")
summarytable(epi_lgc_lin, epi_lgc_quad, epi_lgc_spline,
             which = c("G", "loglik", "AIC", "BIC", "conv"))

best_epi_lgc <- epi_lgc_lin   # selected: linear (lowest BIC)

# ── Step 2: Class enumeration ─────────────────────────────────────────────────
epi_fixed   <- score ~ time
epi_mixture <- ~ time

set.seed(42)
epi_lcga_2 <- gridsearch(
  hlme(epi_fixed, mixture = epi_mixture,
       subject = "id_int", ng = 2, data = epi_long, verbose = FALSE),
  rep = 30, maxiter = 30, minit = best_epi_lgc
)
set.seed(42)
epi_lcga_3 <- gridsearch(
  hlme(epi_fixed, mixture = epi_mixture,
       subject = "id_int", ng = 3, data = epi_long, verbose = FALSE),
  rep = 30, maxiter = 30, minit = best_epi_lgc
)
set.seed(42)
epi_lcga_4 <- gridsearch(
  hlme(epi_fixed, mixture = epi_mixture,
       subject = "id_int", ng = 4, data = epi_long, verbose = FALSE),
  rep = 30, maxiter = 30, minit = best_epi_lgc
)

cat("\nEpiUSA LCGA class enumeration:\n")
summarytable(best_epi_lgc, epi_lcga_2, epi_lcga_3, epi_lcga_4,
             which = c("G", "loglik", "AIC", "BIC", "entropy", "conv"))

for (m in list(epi_lcga_2, epi_lcga_3, epi_lcga_4)) {
  cat("\nEpiUSA class sizes (ng =", m$ng, "):\n")
  print(round(table(m$pprob$class) / nrow(m$pprob) * 100, 1))
}

# ── Selected model: 3-class linear ────────────────────────────────────────────
# Classes: No Depression (76%), Mild Remitting (20%), Moderate Stable (4%)

epi_lcga_3_final <- hlme(score ~ time, mixture = ~ time,
                         subject = "id_int", ng = 3,
                         data = epi_long, verbose = FALSE,
                         B = epi_lcga_3$best)

# ── Trajectory plot ───────────────────────────────────────────────────────────
timeseq_epi <- data.frame(time = seq(0.25, 10, by = 0.1))
pred_epi    <- predictY(epi_lcga_3_final, newdata = timeseq_epi,
                        var.time = "time", draws = TRUE)

pred_epi_df <- data.frame(
  time  = rep(timeseq_epi$time, 3),
  score = c(pred_epi$pred[, "Ypred_class1"],
            pred_epi$pred[, "Ypred_class2"],
            pred_epi$pred[, "Ypred_class3"]),
  lower = c(pred_epi$pred[, "lower.Ypred_class1"],
            pred_epi$pred[, "lower.Ypred_class2"],
            pred_epi$pred[, "lower.Ypred_class3"]),
  upper = c(pred_epi$pred[, "upper.Ypred_class1"],
            pred_epi$pred[, "upper.Ypred_class2"],
            pred_epi$pred[, "upper.Ypred_class3"]),
  class = factor(
    rep(c("Class 2: Mild remitting (20%)",
          "Class 1: No depression (76%)",
          "Class 3: Moderate stable (4%)"),
        each = nrow(timeseq_epi)),
    levels = c("Class 1: No depression (76%)",
               "Class 2: Mild remitting (20%)",
               "Class 3: Moderate stable (4%)")
  )
)

plot_epi <- ggplot(pred_epi_df, aes(x = time, y = score,
                                    colour = class, fill = class)) +
  geom_ribbon(aes(ymin = lower, ymax = upper), alpha = 0.2, colour = NA) +
  geom_line(linewidth = 1.1) +
  geom_hline(yintercept = c(8, 14, 19, 23), linetype = "dotted", colour = "grey70") +
  annotate("text", x = 10, y = c(0, 9.3, 15.3, 20.3, 24.3),
           label = c("No Depression (0-7)", "Mild (8-13)", "Moderate (14-18)",
                     "Severe (19-22)", "Very severe (\u226523)"),
           hjust = 1, size = 7, colour = "grey35") +
  scale_x_continuous(
    breaks = c(0.25, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10),
    labels = c("3mo", "1yr", "2yr", "3yr", "4yr", "5yr", "6yr", "7yr", "8yr", "9yr", "10yr"),
    guide  = guide_axis(angle = 45)
  ) +
  scale_y_continuous(limits = c(0, 30), breaks = seq(0, 30, 5)) +
  scale_colour_manual(values = c(
    "Class 1: No depression (76%)"  = CLASS_COLS["amber"],
    "Class 2: Mild remitting (20%)" = CLASS_COLS["blue"],
    "Class 3: Moderate stable (4%)" = CLASS_COLS["red"]
  )) +
  scale_fill_manual(values = c(
    "Class 1: No depression (76%)"  = CLASS_COLS["amber"],
    "Class 2: Mild remitting (20%)" = CLASS_COLS["blue"],
    "Class 3: Moderate stable (4%)" = CLASS_COLS["red"]
  )) +
  labs(x = "Time post-stroke", y = "HAMD-17 score",
       title = "EpiUSA HAMD: 3-class LCGA",
       colour = NULL, fill = NULL) +
  guides(colour = guide_legend(nrow = 2), fill = guide_legend(nrow = 2)) +
  traj_theme

ggsave(out_path("plot_EpiUSA_HAMD.png"), plot_epi, width = 10, height = 7, dpi = 300)
cat("EpiUSA plot saved.\n")


# =============================================================================
# 6.  SSS — GDS  (n=192)
#
# Timepoints: 6mo (0.5 yr), 1yr, 3yr, 5yr
# =============================================================================

cat("\n────────────────────────────────────────────────────────\n")
cat(" 6. SSS — GDS\n")
cat("────────────────────────────────────────────────────────\n")

# Confirm valid GDS observations before reshaping
cat("SSS patients with ≥1 valid GDS observation: ",
    sum(apply(sss[, c("GDS_t1", "GDS_t2", "GDS_t3", "GDS_t4")], 1,
              function(x) any(!is.na(x)))), "\n")

sss_gds_long <- to_long_lcmm(sss, score_prefix = "GDS", yrs_prefix = "GDS",
                              id_col = "patient_id")
sss_gds_long$id_int <- as.integer(factor(sss_gds_long$patient_id))

cat("SSS GDS long: n_obs =", nrow(sss_gds_long),
    " | n_patients =", n_distinct(sss_gds_long$patient_id), "\n")

# ── Step 1: Functional form ────────────────────────────────────────────────────
sss_gds_lgc_lin <- hlme(score ~ time,
                         subject = "id_int", ng = 1,
                         data = sss_gds_long, verbose = FALSE)

sss_gds_lgc_quad <- hlme(score ~ time + I(time^2),
                          subject = "id_int", ng = 1,
                          data = sss_gds_long, verbose = FALSE)

# Single internal knot at 1 year; sparse data warrants a simple spline
sss_gds_lgc_spline <- hlme(score ~ ns(time, knots = 1),
                             subject = "id_int", ng = 1,
                             data = sss_gds_long, verbose = FALSE)

cat("\nSSS GDS LGC functional form comparison:\n")
summarytable(sss_gds_lgc_lin, sss_gds_lgc_quad, sss_gds_lgc_spline,
             which = c("G", "loglik", "AIC", "BIC", "conv"))

best_sss_gds_lgc <- sss_gds_lgc_lin   # selected: linear

# ── Step 2: Class enumeration ─────────────────────────────────────────────────
sss_gds_fixed   <- score ~ time
sss_gds_mixture <- ~ time

set.seed(42)
sss_gds_lcga_2 <- gridsearch(
  hlme(sss_gds_fixed, mixture = sss_gds_mixture,
       subject = "id_int", ng = 2, data = sss_gds_long, verbose = FALSE),
  rep = 30, maxiter = 30, minit = best_sss_gds_lgc
)
set.seed(42)
sss_gds_lcga_3 <- gridsearch(
  hlme(sss_gds_fixed, mixture = sss_gds_mixture,
       subject = "id_int", ng = 3, data = sss_gds_long, verbose = FALSE),
  rep = 30, maxiter = 30, minit = best_sss_gds_lgc
)
set.seed(42)
sss_gds_lcga_4 <- gridsearch(
  hlme(sss_gds_fixed, mixture = sss_gds_mixture,
       subject = "id_int", ng = 4, data = sss_gds_long, verbose = FALSE),
  rep = 30, maxiter = 30, minit = best_sss_gds_lgc
)

cat("\nSSS GDS LCGA class enumeration:\n")
summarytable(best_sss_gds_lgc, sss_gds_lcga_2, sss_gds_lcga_3, sss_gds_lcga_4,
             which = c("G", "loglik", "AIC", "BIC", "entropy", "conv"))

for (m in list(sss_gds_lcga_2, sss_gds_lcga_3, sss_gds_lcga_4)) {
  cat("\nSSS GDS class sizes (ng =", m$ng, "):\n")
  pct <- round(table(m$pprob$class) / nrow(m$pprob) * 100, 1)
  print(pct)
  if (any(pct < 5)) cat("  *** WARNING: class below 5% ***\n")
}

# ── Selected model: 3-class linear ────────────────────────────────────────────
# Classes: No Depression (72%), Mild Remitting (20%), Moderate Stable (8%)

sss_gds_lcga_3_final <- hlme(score ~ time, mixture = ~ time,
                             subject = "id_int", ng = 3,
                             data = sss_gds_long, verbose = FALSE,
                             B = sss_gds_lcga_3$best)

# ── Trajectory plot ───────────────────────────────────────────────────────────
timeseq_sss <- data.frame(time = seq(0.5, 5, by = 0.05))
pred_sss_gds <- predictY(sss_gds_lcga_3_final, newdata = timeseq_sss,
                         var.time = "time", draws = TRUE)

pred_sss_gds_df <- data.frame(
  time  = rep(timeseq_sss$time, 3),
  score = c(pred_sss_gds$pred[, "Ypred_class1"],
            pred_sss_gds$pred[, "Ypred_class2"],
            pred_sss_gds$pred[, "Ypred_class3"]),
  lower = c(pred_sss_gds$pred[, "lower.Ypred_class1"],
            pred_sss_gds$pred[, "lower.Ypred_class2"],
            pred_sss_gds$pred[, "lower.Ypred_class3"]),
  upper = c(pred_sss_gds$pred[, "upper.Ypred_class1"],
            pred_sss_gds$pred[, "upper.Ypred_class2"],
            pred_sss_gds$pred[, "upper.Ypred_class3"]),
  class = factor(
    rep(c("Class 1: No depression (72%)",
          "Class 3: Moderate stable (8%)",
          "Class 2: Mild remitting (20%)"),
        each = nrow(timeseq_sss)),
    levels = c("Class 1: No depression (72%)",
               "Class 2: Mild remitting (20%)",
               "Class 3: Moderate stable (8%)")
  )
)

plot_sss_gds <- ggplot(pred_sss_gds_df, aes(x = time, y = score,
                                             colour = class, fill = class)) +
  geom_ribbon(aes(ymin = lower, ymax = upper), alpha = 0.2, colour = NA) +
  geom_line(linewidth = 1.1) +
  geom_hline(yintercept = c(5, 9, 12), linetype = "dotted", colour = "grey70") +
  annotate("text", x = 5, y = c(0, 5.7, 9.7, 12.7),
           label = c("No Depression (0-4)", "Mild (5-8)", "Moderate (9-11)", "Severe (\u226512)"),
           hjust = 1, size = 7, colour = "grey35") +
  scale_x_continuous(breaks = c(0.5, 1, 3, 5),
                     labels = c("6mo", "1yr", "3yr", "5yr"),
                     guide  = guide_axis(angle = 45)) +
  scale_y_continuous(limits = c(0, 15), breaks = seq(0, 15, 3)) +
  scale_colour_manual(values = c(
    "Class 1: No depression (72%)"  = CLASS_COLS["amber"],
    "Class 2: Mild remitting (20%)" = CLASS_COLS["blue"],
    "Class 3: Moderate stable (8%)" = CLASS_COLS["red"]
  )) +
  scale_fill_manual(values = c(
    "Class 1: No depression (72%)"  = CLASS_COLS["amber"],
    "Class 2: Mild remitting (20%)" = CLASS_COLS["blue"],
    "Class 3: Moderate stable (8%)" = CLASS_COLS["red"]
  )) +
  labs(x = "Time post-stroke", y = "GDS-15 score",
       title = "SSS GDS: 3-class LCGA",
       colour = NULL, fill = NULL) +
  guides(colour = guide_legend(nrow = 2), fill = guide_legend(nrow = 2)) +
  traj_theme

ggsave(out_path("plot_SSS_GDS.png"), plot_sss_gds, width = 10, height = 7, dpi = 300)
cat("SSS GDS plot saved.\n")


# =============================================================================
# 7.  SSS — HAMD  (n=192)
#
# Timepoints: 6mo (0.5 yr), 1yr, 3yr, 5yr
#
# Note: The 2-class BIC (3068.58) was marginally lower than the 3-class BIC
# (3072.29; ΔBIC = 3.71). The 3-class solution was retained for cross-cohort
# consistency; the ΔBIC is negligible and both solutions have acceptable fit.
# =============================================================================

cat("\n────────────────────────────────────────────────────────\n")
cat(" 7. SSS — HAMD\n")
cat("────────────────────────────────────────────────────────\n")

cat("SSS patients with ≥1 valid HAMD observation: ",
    sum(apply(sss[, c("HAMD_t1", "HAMD_t2", "HAMD_t3", "HAMD_t4")], 1,
              function(x) any(!is.na(x)))), "\n")

sss_hamd_long <- to_long_lcmm(sss, score_prefix = "HAMD", yrs_prefix = "HAMD",
                               id_col = "patient_id")
sss_hamd_long$id_int <- as.integer(factor(sss_hamd_long$patient_id))

cat("SSS HAMD long: n_obs =", nrow(sss_hamd_long),
    " | n_patients =", n_distinct(sss_hamd_long$patient_id), "\n")

# ── Step 1: Functional form ────────────────────────────────────────────────────
sss_hamd_lgc_lin <- hlme(score ~ time,
                          subject = "id_int", ng = 1,
                          data = sss_hamd_long, verbose = FALSE)

sss_hamd_lgc_quad <- hlme(score ~ time + I(time^2),
                           subject = "id_int", ng = 1,
                           data = sss_hamd_long, verbose = FALSE)

sss_hamd_lgc_spline <- hlme(score ~ ns(time, knots = 1),
                              subject = "id_int", ng = 1,
                              data = sss_hamd_long, verbose = FALSE)

cat("\nSSS HAMD LGC functional form comparison:\n")
summarytable(sss_hamd_lgc_lin, sss_hamd_lgc_quad, sss_hamd_lgc_spline,
             which = c("G", "loglik", "AIC", "BIC", "conv"))

best_sss_hamd_lgc <- sss_hamd_lgc_lin   # selected: linear

# ── Step 2: Class enumeration ─────────────────────────────────────────────────
sss_hamd_fixed   <- score ~ time
sss_hamd_mixture <- ~ time

set.seed(42)
sss_hamd_lcga_2 <- gridsearch(
  hlme(sss_hamd_fixed, mixture = sss_hamd_mixture,
       subject = "id_int", ng = 2, data = sss_hamd_long, verbose = FALSE),
  rep = 30, maxiter = 30, minit = best_sss_hamd_lgc
)
set.seed(42)
sss_hamd_lcga_3 <- gridsearch(
  hlme(sss_hamd_fixed, mixture = sss_hamd_mixture,
       subject = "id_int", ng = 3, data = sss_hamd_long, verbose = FALSE),
  rep = 30, maxiter = 30, minit = best_sss_hamd_lgc
)
set.seed(42)
sss_hamd_lcga_4 <- gridsearch(
  hlme(sss_hamd_fixed, mixture = sss_hamd_mixture,
       subject = "id_int", ng = 4, data = sss_hamd_long, verbose = FALSE),
  rep = 30, maxiter = 30, minit = best_sss_hamd_lgc
)

cat("\nSSS HAMD LCGA class enumeration:\n")
summarytable(best_sss_hamd_lgc, sss_hamd_lcga_2, sss_hamd_lcga_3, sss_hamd_lcga_4,
             which = c("G", "loglik", "AIC", "BIC", "entropy", "conv"))

for (m in list(sss_hamd_lcga_2, sss_hamd_lcga_3, sss_hamd_lcga_4)) {
  cat("\nSSS HAMD class sizes (ng =", m$ng, "):\n")
  pct <- round(table(m$pprob$class) / nrow(m$pprob) * 100, 1)
  print(pct)
  if (any(pct < 5)) cat("  *** WARNING: class below 5% ***\n")
}

# ── Selected model: 3-class linear ────────────────────────────────────────────
# Classes: No Depression (83%), Moderate Remitting (14%), Mild Worsening (4%)

sss_hamd_lcga_3_final <- hlme(score ~ time, mixture = ~ time,
                              subject = "id_int", ng = 3,
                              data = sss_hamd_long, verbose = FALSE,
                              B = sss_hamd_lcga_3$best)

# ── Trajectory plot ───────────────────────────────────────────────────────────
timeseq_sss_hamd <- data.frame(time = seq(0.5, 5, by = 0.05))
pred_sss_hamd    <- predictY(sss_hamd_lcga_3_final, newdata = timeseq_sss_hamd,
                              var.time = "time", draws = TRUE)

pred_sss_hamd_df <- data.frame(
  time  = rep(timeseq_sss_hamd$time, 3),
  score = c(pred_sss_hamd$pred[, "Ypred_class1"],
            pred_sss_hamd$pred[, "Ypred_class2"],
            pred_sss_hamd$pred[, "Ypred_class3"]),
  lower = c(pred_sss_hamd$pred[, "lower.Ypred_class1"],
            pred_sss_hamd$pred[, "lower.Ypred_class2"],
            pred_sss_hamd$pred[, "lower.Ypred_class3"]),
  upper = c(pred_sss_hamd$pred[, "upper.Ypred_class1"],
            pred_sss_hamd$pred[, "upper.Ypred_class2"],
            pred_sss_hamd$pred[, "upper.Ypred_class3"]),
  class = factor(
    rep(c("Class 1: No depression (83%)",
          "Class 2: Moderate remitting (14%)",
          "Class 3: Mild worsening (4%)"),
        each = nrow(timeseq_sss_hamd)),
    levels = c("Class 1: No depression (83%)",
               "Class 2: Moderate remitting (14%)",
               "Class 3: Mild worsening (4%)")
  )
)

plot_sss_hamd <- ggplot(pred_sss_hamd_df, aes(x = time, y = score,
                                              colour = class, fill = class)) +
  geom_ribbon(aes(ymin = lower, ymax = upper), alpha = 0.2, colour = NA) +
  geom_line(linewidth = 1.1) +
  geom_hline(yintercept = c(8, 14, 19, 23), linetype = "dotted", colour = "grey70") +
  annotate("text", x = 5, y = c(0, 9.2, 15.2, 20.2, 24.2),
           label = c("No Depression (0-7)", "Mild (8-13)", "Moderate (14-18)",
                     "Severe (19-22)", "Very severe (\u226523)"),
           hjust = 1, size = 7, colour = "grey35") +
  scale_x_continuous(breaks = c(0.5, 1, 3, 5),
                     labels = c("6mo", "1yr", "3yr", "5yr"),
                     guide  = guide_axis(angle = 45)) +
  scale_y_continuous(limits = c(0, 30), breaks = seq(0, 30, 5)) +
  scale_colour_manual(values = c(
    "Class 1: No depression (83%)"      = CLASS_COLS["amber"],
    "Class 2: Moderate remitting (14%)" = CLASS_COLS["blue"],
    "Class 3: Mild worsening (4%)"      = CLASS_COLS["red"]
  )) +
  scale_fill_manual(values = c(
    "Class 1: No depression (83%)"      = CLASS_COLS["amber"],
    "Class 2: Moderate remitting (14%)" = CLASS_COLS["blue"],
    "Class 3: Mild worsening (4%)"      = CLASS_COLS["red"]
  )) +
  labs(x = "Time post-stroke", y = "HAMD-17 score",
       title = "SSS HAMD: 3-class LCGA",
       colour = NULL, fill = NULL) +
  guides(colour = guide_legend(nrow = 2), fill = guide_legend(nrow = 2)) +
  traj_theme

ggsave(out_path("plot_SSS_HAMD.png"), plot_sss_hamd, width = 10, height = 7, dpi = 300)
cat("SSS HAMD plot saved.\n")


# =============================================================================
# 8.  POOLED HAMD — EpiUSA + SSS  (primary pooled analysis; n=665)
#
# Cohort dummy: 0 = EpiUSA, 1 = SSS
#
# Within-cohort T-score standardisation (mean=50, SD=10) applied to the
# input dataset (dataset_pooled_HAMD.csv) to remove cohort mean differences
# before modelling. Trajectories are back-transformed to HAMD-17 raw scores
# for plotting using the EpiUSA distribution parameters:
#   mean = 4.2042, SD = 4.5870
#
# Cohort is included as a fixed covariate but NOT in the mixture formula,
# so trajectory shapes are constrained to be equal across cohorts.
# =============================================================================

cat("\n────────────────────────────────────────────────────────\n")
cat(" 8. Pooled HAMD (EpiUSA + SSS)\n")
cat("────────────────────────────────────────────────────────\n")

pooled$cohort <- as.integer(pooled$study == "SSS")   # 0 = EpiUSA, 1 = SSS
pooled$id_int <- as.integer(factor(pooled$patient_id))

cat("Pooled HAMD: n_obs =", nrow(pooled),
    " | n_patients =", n_distinct(pooled$patient_id), "\n")

# Verify T-score standardisation (should give mean≈50, SD≈10 per cohort)
cat("T-score check by cohort:\n")
print(pooled %>%
        group_by(study) %>%
        summarise(mean_T = round(mean(HAMD_T, na.rm = TRUE), 2),
                  sd_T   = round(sd(HAMD_T,   na.rm = TRUE), 2)))

# ── Step 1: Functional form ────────────────────────────────────────────────────
pool_lgc_lin <- hlme(HAMD_T ~ time_yrs + cohort,
                     subject = "id_int", ng = 1,
                     data = pooled, verbose = FALSE)

pool_lgc_quad <- hlme(HAMD_T ~ time_yrs + I(time_yrs^2) + cohort,
                      subject = "id_int", ng = 1,
                      data = pooled, verbose = FALSE)

pool_lgc_spline <- hlme(HAMD_T ~ ns(time_yrs, knots = c(1, 3)) + cohort,
                         subject = "id_int", ng = 1,
                         data = pooled, verbose = FALSE)

cat("\nPooled HAMD LGC functional form comparison:\n")
summarytable(pool_lgc_lin, pool_lgc_quad, pool_lgc_spline,
             which = c("G", "loglik", "AIC", "BIC", "conv"))

best_pool_lgc <- pool_lgc_lin   # selected: linear

# ── Step 2: Class enumeration ─────────────────────────────────────────────────
pool_fixed   <- HAMD_T ~ time_yrs + cohort
pool_mixture <- ~ time_yrs

set.seed(42)
pool_lcga_2 <- gridsearch(
  hlme(pool_fixed, mixture = pool_mixture,
       subject = "id_int", ng = 2, data = pooled, verbose = FALSE),
  rep = 30, maxiter = 30, minit = best_pool_lgc
)
set.seed(42)
pool_lcga_3 <- gridsearch(
  hlme(pool_fixed, mixture = pool_mixture,
       subject = "id_int", ng = 3, data = pooled, verbose = FALSE),
  rep = 30, maxiter = 30, minit = best_pool_lgc
)
set.seed(42)
pool_lcga_4 <- gridsearch(
  hlme(pool_fixed, mixture = pool_mixture,
       subject = "id_int", ng = 4, data = pooled, verbose = FALSE),
  rep = 30, maxiter = 30, minit = best_pool_lgc
)

cat("\nPooled HAMD LCGA class enumeration:\n")
summarytable(best_pool_lgc, pool_lcga_2, pool_lcga_3, pool_lcga_4,
             which = c("G", "loglik", "AIC", "BIC", "entropy", "conv"))

for (m in list(pool_lcga_2, pool_lcga_3, pool_lcga_4)) {
  cat("\nPooled HAMD class sizes (ng =", m$ng, "):\n")
  pct <- round(table(m$pprob$class) / nrow(m$pprob) * 100, 1)
  print(pct)
  tmp <- merge(m$pprob[, c("id_int", "class")],
               pooled[!duplicated(pooled$id_int), c("id_int", "study")])
  cat("  By cohort:\n"); print(table(tmp$study, tmp$class))
}

# ── Selected model: 3-class linear ────────────────────────────────────────────
# Classes: No Depression (78%), Mild Remitting (19%), Moderate Improving (4%)

# ── Trajectory plot (back-transformed to HAMD-17 raw scores) ─────────────────
# Model fixed-effect intercepts and slopes extracted from pool_lcga_3.
# Back-transformation: raw = (T_score - 50) / 10 * SD_EpiUSA + mean_EpiUSA
#   where mean_EpiUSA = 4.2042, SD_EpiUSA = 4.5870

hamd_mean <- 4.2042
hamd_sd   <- 4.5870

# Standard-error function for linear trajectory CIs
se_linear <- function(t, var_int, var_slope, cov_is) {
  sqrt(var_int + t^2 * var_slope + 2 * t * cov_is) / 10 * hamd_sd
}

t_seq <- seq(0.25, 10, by = 0.1)

pool_plot_df <- data.frame(
  time_yrs = rep(t_seq, 3),
  hamd = c(
    ((46.96536 + (-0.17973) * t_seq) - 50) / 10 * hamd_sd + hamd_mean,   # Class 1
    ((61.99734 + (-1.46258) * t_seq) - 50) / 10 * hamd_sd + hamd_mean,   # Class 2
    ((75.64169 + (-0.94705) * t_seq) - 50) / 10 * hamd_sd + hamd_mean    # Class 3
  ),
  se = c(
    se_linear(t_seq, 0.121151, 0.008762, -0.020667),
    se_linear(t_seq, 0.801018, 0.055306, -0.136640),
    se_linear(t_seq, 2.280403, 0.279397, -0.584905)
  ),
  class = rep(c(
    "Class 1: No depression (78%)",
    "Class 2: Mild remitting (19%)",
    "Class 3: Moderate improving (4%)"
  ), each = length(t_seq))
) %>%
  mutate(lower = hamd - 1.96 * se, upper = hamd + 1.96 * se)

plot_pool_hamd <- ggplot(pool_plot_df, aes(x = time_yrs, y = hamd,
                                           colour = class, fill = class, group = class)) +
  geom_ribbon(aes(ymin = lower, ymax = upper), alpha = 0.2, colour = NA) +
  geom_line(linewidth = 1.2) +
  geom_hline(yintercept = c(8, 14, 19, 23), linetype = "dotted", colour = "grey70") +
  annotate("text", x = 10, y = c(0, 9.2, 15.2, 20.2, 24.2),
           label = c("No Depression (0-7)", "Mild (8-13)", "Moderate (14-18)",
                     "Severe (19-22)", "Very severe (\u226523)"),
           hjust = 1, size = 7, colour = "grey35") +
  scale_x_continuous(
    breaks = c(0.2, 0.6, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10),
    labels = c("3mo", "6mo", "1yr", "2yr", "3yr", "4yr", "5yr",
               "6yr", "7yr", "8yr", "9yr", "10yr"),
    guide  = guide_axis(angle = 45)
  ) +
  scale_y_continuous(limits = c(0, 30), breaks = seq(0, 30, 5)) +
  scale_colour_manual(values = c(
    "Class 1: No depression (78%)"      = CLASS_COLS["amber"],
    "Class 2: Mild remitting (19%)"     = CLASS_COLS["blue"],
    "Class 3: Moderate improving (4%)"  = CLASS_COLS["red"]
  )) +
  scale_fill_manual(values = c(
    "Class 1: No depression (78%)"      = CLASS_COLS["amber"],
    "Class 2: Mild remitting (19%)"     = CLASS_COLS["blue"],
    "Class 3: Moderate improving (4%)"  = CLASS_COLS["red"]
  )) +
  labs(x = "Time post-stroke", y = "HAMD-17 score",
       title = "Pooled HAMD: 3-class LCGA",
       colour = NULL, fill = NULL) +
  guides(colour = guide_legend(nrow = 2), fill = guide_legend(nrow = 2)) +
  traj_theme

ggsave(out_path("plot_Pooled_HAMD.png"), plot_pool_hamd,
       width = 10, height = 7, dpi = 300)
cat("Pooled HAMD plot saved.\n")


# =============================================================================
# 9.  POOLED GDS — PSS + SSS  (secondary pooled analysis; n=277)
#
# Cohort dummy: 0 = PSS, 1 = SSS
#
# PSS contributes the acute phase (5-day to 24-months).
# SSS contributes the chronic phase (6-months to 5-years).
# Overlap window: 6-months and 12-months.
#
# Back-transformation parameters (PSS distribution):
#   mean = 3.9412, SD = 3.2691
# =============================================================================

cat("\n────────────────────────────────────────────────────────\n")
cat(" 9. Pooled GDS (PSS + SSS)\n")
cat("────────────────────────────────────────────────────────\n")

pooled_gds$cohort <- as.integer(pooled_gds$study == "SSS")   # 0 = PSS, 1 = SSS

cat("Pooled GDS: n_obs =", nrow(pooled_gds),
    " | n_patients =", n_distinct(pooled_gds$patient_id), "\n")

cat("T-score check (should be mean≈50, SD≈10 per cohort):\n")
print(pooled_gds %>%
        group_by(study) %>%
        summarise(mean_T = round(mean(GDS_T, na.rm = TRUE), 2),
                  sd_T   = round(sd(GDS_T,   na.rm = TRUE), 2),
                  n_obs  = n()))

# ── Step 1: Functional form ────────────────────────────────────────────────────
# Spline knots chosen to capture:
#   0.0833 (1-month) — acute-phase inflection (PSS)
#   0.5    (6-months) — shared overlap window; transition to chronic phase
#   1.0    (1-year)   — mid-point of SSS follow-up
pgds_lgc_lin <- hlme(GDS_T ~ time_yrs + cohort,
                     subject = "id_int", ng = 1,
                     data = pooled_gds, verbose = FALSE)

pgds_lgc_quad <- hlme(GDS_T ~ time_yrs + I(time_yrs^2) + cohort,
                      subject = "id_int", ng = 1,
                      data = pooled_gds, verbose = FALSE)

pgds_lgc_spline <- hlme(GDS_T ~ ns(time_yrs, knots = c(1/12, 0.5, 1)) + cohort,
                         subject = "id_int", ng = 1,
                         data = pooled_gds, verbose = FALSE)

cat("\nPooled GDS LGC functional form comparison:\n")
summarytable(pgds_lgc_lin, pgds_lgc_quad, pgds_lgc_spline,
             which = c("G", "loglik", "AIC", "BIC", "conv"))

best_pgds_lgc <- pgds_lgc_lin   # selected: linear

# ── Step 2: Class enumeration ─────────────────────────────────────────────────
pgds_fixed   <- GDS_T ~ time_yrs + cohort
pgds_mixture <- ~ time_yrs

set.seed(42)
pgds_lcga_2 <- gridsearch(
  hlme(pgds_fixed, mixture = pgds_mixture,
       subject = "id_int", ng = 2, data = pooled_gds, verbose = FALSE),
  rep = 30, maxiter = 30, minit = best_pgds_lgc
)
set.seed(42)
pgds_lcga_3 <- gridsearch(
  hlme(pgds_fixed, mixture = pgds_mixture,
       subject = "id_int", ng = 3, data = pooled_gds, verbose = FALSE),
  rep = 30, maxiter = 30, minit = best_pgds_lgc
)
set.seed(42)
pgds_lcga_4 <- gridsearch(
  hlme(pgds_fixed, mixture = pgds_mixture,
       subject = "id_int", ng = 4, data = pooled_gds, verbose = FALSE),
  rep = 30, maxiter = 30, minit = best_pgds_lgc
)

cat("\nPooled GDS LCGA class enumeration:\n")
summarytable(best_pgds_lgc, pgds_lcga_2, pgds_lcga_3, pgds_lcga_4,
             which = c("G", "loglik", "AIC", "BIC", "entropy", "conv"))

for (m in list(pgds_lcga_2, pgds_lcga_3, pgds_lcga_4)) {
  cat("\nPooled GDS class sizes (ng =", m$ng, "):\n")
  print(round(table(m$pprob$class) / nrow(m$pprob) * 100, 1))
  print(table(m$pprob$class,
              pooled_gds[!duplicated(pooled_gds$id_int), "study"]))
}

# ── Selected model: 3-class linear ────────────────────────────────────────────
# Classes: No Depression (65%), Mild Remitting (25%), Moderate Stable (10%)

# ── Trajectory plot (back-transformed to GDS-15 raw scores) ──────────────────
gds_mean <- 3.9412
gds_sd   <- 3.2691

se_linear_gds <- function(t, var_int, var_slope, cov_is) {
  sqrt(var_int + t^2 * var_slope + 2 * t * cov_is) / 10 * gds_sd
}

t_seq_gds <- seq(0.0137, 5, by = 0.01)

pgds_plot_df <- data.frame(
  time_yrs = rep(t_seq_gds, 3),
  gds = c(
    # Class 1: No Depression  (model class 2: intercept=44.37, slope=−0.00148)
    ((44.37257 + (-0.00148) * t_seq_gds) - 50) / 10 * gds_sd + gds_mean,
    # Class 2: Mild Remitting  (model class 1: intercept=56.50, slope=−1.151)
    ((56.50257 + (-1.15122) * t_seq_gds) - 50) / 10 * gds_sd + gds_mean,
    # Class 3: Moderate Stable (model class 3: intercept=70.12, slope=+0.097)
    ((70.12173 + (0.09748)  * t_seq_gds) - 50) / 10 * gds_sd + gds_mean
  ),
  se = c(
    se_linear_gds(t_seq_gds, 0.248654, 0.014043, -0.008246),
    se_linear_gds(t_seq_gds, 0.865269, 0.137743, -0.192036),
    se_linear_gds(t_seq_gds, 1.968786, 0.443708, -0.530965)
  ),
  class = rep(c(
    "Class 1: No depression (65%)",
    "Class 2: Mild remitting (25%)",
    "Class 3: Moderate stable (10%)"
  ), each = length(t_seq_gds))
) %>%
  mutate(lower = gds - 1.96 * se, upper = gds + 1.96 * se)

plot_pool_gds <- ggplot(pgds_plot_df, aes(x = time_yrs, y = gds,
                                          colour = class, fill = class, group = class)) +
  geom_ribbon(aes(ymin = lower, ymax = upper), alpha = 0.2, colour = NA) +
  geom_line(linewidth = 1.1) +
  geom_hline(yintercept = c(5, 9, 12), linetype = "dotted", colour = "grey70") +
  annotate("text", x = 5, y = c(0, 5.7, 9.7, 12.7),
           label = c("No Depression (0-4)", "Mild (5-8)", "Moderate (9-11)", "Severe (\u226512)"),
           hjust = 1, size = 7, colour = "grey35") +
  scale_x_continuous(
    breaks = c(0, 0.25, 0.6, 1, 2, 3, 5),
    labels = c("5d", "1mo", "6mo", "1yr", "2yr", "3yr", "5yr"),
    guide  = guide_axis(angle = 45)
  ) +
  scale_y_continuous(limits = c(0, 15), breaks = seq(0, 15, 3)) +
  scale_colour_manual(values = c(
    "Class 1: No depression (65%)"    = CLASS_COLS["amber"],
    "Class 2: Mild remitting (25%)"   = CLASS_COLS["blue"],
    "Class 3: Moderate stable (10%)"  = CLASS_COLS["red"]
  )) +
  scale_fill_manual(values = c(
    "Class 1: No depression (65%)"    = CLASS_COLS["amber"],
    "Class 2: Mild remitting (25%)"   = CLASS_COLS["blue"],
    "Class 3: Moderate stable (10%)"  = CLASS_COLS["red"]
  )) +
  labs(x = "Time post-stroke", y = "GDS-15 score",
       title = "Pooled GDS: 3-class LCGA",
       colour = NULL, fill = NULL) +
  guides(colour = guide_legend(nrow = 2), fill = guide_legend(nrow = 2)) +
  traj_theme

ggsave(out_path("plot_Pooled_GDS.png"), plot_pool_gds,
       width = 10, height = 7, dpi = 300)
cat("Pooled GDS plot saved.\n")


# =============================================================================
# 10.  EXPORT CLASS ASSIGNMENTS
# =============================================================================
# Saves posterior class probabilities and modal class assignment for each
# participant. Used as input to BCH regression (Section 11).

best_models <- list(
  PSS_GDS     = pss_lcga_3,
  EpiUSA_HAMD = epi_lcga_3,
  SSS_GDS     = sss_gds_lcga_3,
  SSS_HAMD    = sss_hamd_lcga_3,
  Pooled_HAMD = pool_lcga_3,
  Pooled_GDS  = pgds_lcga_3
)

for (nm in names(best_models)) {
  out_df <- best_models[[nm]]$pprob
  write.csv(out_df, out_path(paste0("class_assignments_", nm, ".csv")),
            row.names = FALSE)
  cat("Saved class assignments:", nm, "| n =", nrow(out_df), "\n")
}


# =============================================================================
# 11.  BCH REGRESSION — Predictors of Trajectory Class Membership
#
# Method: BCH (Bolck-Croon-Hagenaars) correction accounts for classification
#   uncertainty by re-weighting observations using the inverse of the
#   classification error matrix.  Each pairwise contrast (Class k vs Class 1)
#   is fit as a separate weighted linear model with the BCH weight for class k
#   as the outcome and (bch1 + bch_k) as case weights.
#   Reference: Bolck et al. (2004, Polit Analysis);
#              Vermunt (2010, Sociol Methodol)
#
# Predictors (theory-driven, pre-specified):
#   - Age                : associated with depression severity post-stroke
#   - Sex (female)       : robust predictor of PSD (Hackett & Pickles, 2014)
#   - Hypertension       : vascular depression hypothesis (Alexopoulos et al., 1997)
#   - Diabetes           : independent association with PSD (Ayerbe et al., 2013)
#   - Global cognition z : consistent predictor of PSD (Villa et al., 2018)
#   - Cohort dummy       : controls for residual cohort-level differences
#
# Note: Prior depression excluded due to high missingness in EpiUSA (n=158, 33%)
#       and unavailability in PSS.
#
# PRIMARY:   Pooled HAMD (EpiUSA + SSS; n=665; cohort: 0=EpiUSA, 1=SSS)
# SECONDARY: Pooled GDS  (PSS + SSS;    n=277; cohort: 0=PSS,    1=SSS)
# =============================================================================

# ── Helper: format BCH regression output ──────────────────────────────────────
format_bch <- function(model, contrast_label) {
  tidy(model, conf.int = TRUE) %>%
    filter(term != "(Intercept)") %>%
    mutate(
      contrast = contrast_label,
      term = recode(term,
        age          = "Age",
        sex_female   = "Sex (female)",
        hypertension = "Hypertension",
        diabetes     = "Diabetes",
        zglobal      = "Global cognition (z)",
        cohort       = "Cohort"
      ),
      p_star = case_when(
        p.value < .001 ~ "***",
        p.value < .01  ~ "**",
        p.value < .05  ~ "*",
        p.value < .10  ~ "\u2020",
        TRUE           ~ ""
      ),
      result = sprintf("%.3f [%.3f, %.3f]%s",
                       estimate, conf.low, conf.high, p_star)
    ) %>%
    select(contrast, term, estimate, conf.low, conf.high, p.value, p_star, result)
}

# ── BCH weight computation (shared function) ──────────────────────────────────
compute_bch_weights <- function(lcga_model) {
  pprob <- lcga_model$pprob
  ng    <- lcga_model$ng
  P     <- as.matrix(pprob[, paste0("prob", 1:ng)])
  C     <- matrix(0, nrow = ng, ncol = ng)
  for (j in 1:ng) {
    idx    <- pprob$class == j
    C[j, ] <- colMeans(P[idx, ])
  }
  cat("Classification error matrix:\n"); print(round(C, 3))
  W           <- P %*% solve(C)
  W[W < 0]    <- 0                      # clip small negative values to zero
  colnames(W) <- paste0("bch", 1:ng)
  cbind(pprob %>% select(id_int, class), as.data.frame(W))
}

# =============================================================================
# 11a.  PRIMARY: Pooled HAMD BCH Regression
# =============================================================================

cat("\n=============================================================\n")
cat(" PRIMARY: Pooled HAMD BCH Regression (EpiUSA + SSS)\n")
cat("=============================================================\n")

bch_df_hamd <- compute_bch_weights(pool_lcga_3)

baseline_hamd <- pooled %>%
  group_by(id_int) %>%
  slice(1) %>%
  ungroup() %>%
  select(id_int, patient_id, study, age, sex, hypertension, diabetes,
         zglobal, cohort)

reg_data_hamd <- bch_df_hamd %>%
  left_join(baseline_hamd, by = "id_int") %>%
  mutate(
    sex_female   = as.integer(sex == "female"),
    hypertension = as.integer(hypertension == 1 | hypertension == TRUE),
    diabetes     = as.integer(diabetes     == 1 | diabetes     == TRUE)
  )

cat("\nComplete cases on all predictors:\n")
cat("  n =",
    sum(complete.cases(reg_data_hamd %>%
                         select(age, sex_female, hypertension, diabetes,
                                zglobal, cohort))),
    "of", nrow(reg_data_hamd), "\n")

# Class 2 (Mild Remitting) vs Class 1 (No Depression)
bch_hamd_c2v1 <- lm(bch2 ~ age + sex_female + hypertension + diabetes +
                      zglobal + cohort,
                    data    = reg_data_hamd,
                    weights = (bch1 + bch2))
summary(bch_hamd_c2v1)

# Class 3 (Moderate Improving) vs Class 1 (No Depression)
bch_hamd_c3v1 <- lm(bch3 ~ age + sex_female + hypertension + diabetes +
                      zglobal + cohort,
                    data    = reg_data_hamd,
                    weights = (bch1 + bch3))
summary(bch_hamd_c3v1)

res_hamd <- bind_rows(
  format_bch(bch_hamd_c2v1, "Class 2 (Mild Remitting) vs Class 1 (No Depression)"),
  format_bch(bch_hamd_c3v1, "Class 3 (Moderate Improving) vs Class 1 (No Depression)")
)

cat("\n=== POOLED HAMD: BCH Regression Results ===\n")
print(as.data.frame(res_hamd %>% select(contrast, term, result)), row.names = FALSE)

write.csv(res_hamd, out_path("bch_results_pooled_HAMD.csv"), row.names = FALSE)
cat("Saved: bch_results_pooled_HAMD.csv\n")


# =============================================================================
# 11b.  SECONDARY: Pooled GDS BCH Regression
# =============================================================================

cat("\n=============================================================\n")
cat(" SECONDARY: Pooled GDS BCH Regression (PSS + SSS)\n")
cat("=============================================================\n")

bch_df_gds <- compute_bch_weights(pgds_lcga_3)

baseline_gds <- pooled_gds %>%
  group_by(id_int) %>%
  slice(1) %>%
  ungroup() %>%
  select(id_int, patient_id, study, age, sex, hypertension, diabetes,
         zglobal, cohort)

reg_data_gds <- bch_df_gds %>%
  left_join(baseline_gds, by = "id_int") %>%
  mutate(
    sex_female   = as.integer(sex == "female"),
    hypertension = as.integer(hypertension == 1 | hypertension == TRUE),
    diabetes     = as.integer(diabetes     == 1 | diabetes     == TRUE)
  )

cat("\nComplete cases on all predictors:\n")
cat("  n =",
    sum(complete.cases(reg_data_gds %>%
                         select(age, sex_female, hypertension, diabetes,
                                zglobal, cohort))),
    "of", nrow(reg_data_gds), "\n")

# Class 2 (Mild Remitting) vs Class 1 (No Depression)
bch_gds_c2v1 <- lm(bch2 ~ age + sex_female + hypertension + diabetes +
                     zglobal + cohort,
                   data    = reg_data_gds,
                   weights = (bch1 + bch2))
summary(bch_gds_c2v1)

# Class 3 (Moderate Persistent) vs Class 1 (No Depression)
bch_gds_c3v1 <- lm(bch3 ~ age + sex_female + hypertension + diabetes +
                     zglobal + cohort,
                   data    = reg_data_gds,
                   weights = (bch1 + bch3))
summary(bch_gds_c3v1)

res_gds <- bind_rows(
  format_bch(bch_gds_c2v1, "Class 2 (Mild Remitting) vs Class 1 (No Depression)"),
  format_bch(bch_gds_c3v1, "Class 3 (Moderate Persistent) vs Class 1 (No Depression)")
)

cat("\n=== POOLED GDS: BCH Regression Results ===\n")
print(as.data.frame(res_gds %>% select(contrast, term, result)), row.names = FALSE)

write.csv(res_gds, out_path("bch_results_pooled_GDS.csv"), row.names = FALSE)
cat("Saved: bch_results_pooled_GDS.csv\n")


# =============================================================================
# 12.  SUPPLEMENTARY EXTENDED BCH REGRESSION — Pooled HAMD (EpiUSA + SSS)
#
# Extends the primary BCH regression by adding stroke-related predictors.
# Conducted for pooled HAMD only — stroke characteristics unavailable in PSS
# and incomplete in EpiUSA and SSS, reducing the analytic sample to n=473.
#
# Additional predictors:
#   - Prior stroke (yes vs no)
#   - Stroke type (TIA vs Ischaemic; reference)
#   - Lesion location (Left/Infratentorial vs Right; reference)
#   - Stroke subtype (Small vessel/Cardioembolic/Undetermined/Other
#                     vs Large artery; reference)
#
# Note: Stroke type (TIA) could not be estimated — TIA occurred exclusively
#       in SSS, rendering it collinear with cohort.
#
# Requires: pool_lcga_3, pooled, master_PSD_dataset_n750.csv
# =============================================================================

library(broom)

# ── Load master dataset with stroke characteristics ───────────────────────────
# master_n750 must include lesion_location, strokesubtype, stroke_prior
# (created by the data preparation script)
master_n750 <- read.csv(data_path("master_PSD_dataset_n750.csv"),
                         stringsAsFactors = FALSE)

# ── Prepare extended predictor dataset ───────────────────────────────────────
pooled$cohort <- as.integer(pooled$study == "SSS")   # 0 = EpiUSA, 1 = SSS
pooled$id_int <- as.integer(factor(pooled$patient_id))

baseline_ext <- pooled %>%
  group_by(id_int) %>%
  slice(1) %>%
  ungroup() %>%
  select(id_int, patient_id, study, age, sex, hypertension, diabetes,
         zglobal, cohort) %>%
  left_join(
    master_n750 %>% select(patient_id, stroke_prior, stroketype,
                            lesion_location, strokesubtype),
    by = "patient_id"
  ) %>%
  mutate(
    sex_female        = as.integer(sex == "female"),
    hypertension      = as.integer(hypertension == 1 | hypertension == TRUE),
    diabetes          = as.integer(diabetes == 1 | diabetes == TRUE),
    stroke_prior      = as.integer(stroke_prior == "Yes"),
    # Stroke type: TIA vs Ischaemic (reference)
    # NOTE: collinear with cohort (TIA = SSS only) — will produce NA in model
    stroke_TIA        = as.integer(stroketype == "TIA"),
    # Lesion location: reference = Right hemisphere
    lesion_Left       = as.integer(lesion_location == "Left"),
    lesion_Infra      = as.integer(lesion_location == "Infratentorial"),
    # Stroke subtype: reference = Large artery
    sub_SmallVessel   = as.integer(strokesubtype == "Small vessel"),
    sub_Cardioembolic = as.integer(strokesubtype == "Cardioembolic"),
    sub_Undetermined  = as.integer(strokesubtype == "Undetermined"),
    sub_Other         = as.integer(strokesubtype == "Other")
  )

cat("Complete cases on extended predictor set:\n")
cat("  n =", sum(complete.cases(baseline_ext %>%
      select(age, sex_female, hypertension, diabetes, zglobal, cohort,
             stroke_prior, stroke_TIA, lesion_Left, lesion_Infra,
             sub_SmallVessel, sub_Cardioembolic, sub_Undetermined,
             sub_Other))),
    "of", nrow(baseline_ext), "\n")

# ── Recompute BCH weights for pooled HAMD ─────────────────────────────────────
# (recompute here in case environment was restarted)
pprob_hamd_ext <- pool_lcga_3$pprob %>% select(id_int, class)
P_hamd_ext     <- as.matrix(pool_lcga_3$pprob[, c("prob1", "prob2", "prob3")])
C_hamd_ext     <- matrix(0, nrow = 3, ncol = 3)
for (j in 1:3) {
  C_hamd_ext[j, ] <- colMeans(P_hamd_ext[pprob_hamd_ext$class == j, ])
}
W_hamd_ext           <- P_hamd_ext %*% solve(C_hamd_ext)
W_hamd_ext[W_hamd_ext < 0] <- 0
colnames(W_hamd_ext) <- c("bch1", "bch2", "bch3")
bch_df_ext <- cbind(pprob_hamd_ext %>% select(id_int, class),
                    as.data.frame(W_hamd_ext))

# ── Merge BCH weights with extended predictor data ────────────────────────────
reg_data_ext <- bch_df_ext %>% left_join(baseline_ext, by = "id_int")

# ── BCH: Class 2 (Mild Remitting) vs Class 1 (No Depression) ─────────────────
cat("\n--- Extended BCH: Class 2 (Mild Remitting) vs Class 1 ---\n")
bch_ext_c2v1 <- lm(
  bch2 ~ age + sex_female + hypertension + diabetes + zglobal + cohort +
         stroke_prior + stroke_TIA +
         lesion_Left + lesion_Infra +
         sub_SmallVessel + sub_Cardioembolic + sub_Undetermined + sub_Other,
  data    = reg_data_ext,
  weights = (bch1 + bch2)
)
summary(bch_ext_c2v1)

# ── BCH: Class 3 (Moderate Improving) vs Class 1 (No Depression) ─────────────
cat("\n--- Extended BCH: Class 3 (Moderate Improving) vs Class 1 ---\n")
bch_ext_c3v1 <- lm(
  bch3 ~ age + sex_female + hypertension + diabetes + zglobal + cohort +
         stroke_prior + stroke_TIA +
         lesion_Left + lesion_Infra +
         sub_SmallVessel + sub_Cardioembolic + sub_Undetermined + sub_Other,
  data    = reg_data_ext,
  weights = (bch1 + bch3)
)
summary(bch_ext_c3v1)

# ── Format and export results ──────────────────────────────────────────────────
res_ext <- bind_rows(
  format_bch(bch_ext_c2v1, "Class 2 (Mild Remitting) vs Class 1 (No Depression)"),
  format_bch(bch_ext_c3v1, "Class 3 (Moderate Improving) vs Class 1 (No Depression)")
) %>%
  mutate(term = recode(term,
    stroke_prior      = "Prior stroke",
    stroke_TIA        = "Stroke type (TIA vs Ischaemic)",
    lesion_Left       = "Lesion location (Left vs Right)",
    lesion_Infra      = "Lesion location (Infratentorial vs Right)",
    sub_SmallVessel   = "Subtype (Small vessel vs Large artery)",
    sub_Cardioembolic = "Subtype (Cardioembolic vs Large artery)",
    sub_Undetermined  = "Subtype (Undetermined vs Large artery)",
    sub_Other         = "Subtype (Other vs Large artery)"
  ))

cat("\n=== SUPPLEMENTARY: Extended BCH Regression Results ===\n")
print(as.data.frame(res_ext %>% select(contrast, term, result)), row.names = FALSE)

write.csv(res_ext, out_path("bch_results_supplementary.csv"), row.names = FALSE)
cat("Saved: bch_results_supplementary.csv\n")


cat("\n\nAll analyses complete.\n")
cat("Output files written to:", OUT_DIR, "\n")
