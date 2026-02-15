/**
 * @file trit_trunc_mul.h
 * @brief seT6 Truncated Balanced Ternary Multiplier (Parhami)
 *
 * Balanced ternary truncated multiplication achieves error < 0.5 ulp
 * with 22% area reduction — the same relative savings as binary truncation
 * but with zero error bias (balanced digits {-1,0,+1} average to 0).
 *
 * Reference: Cook/Parhami, "Lower-Error Truncated Multiplication"
 *
 * Key insight: When chopping least-significant partial product trits in
 * balanced ternary, the expected value of each dropped trit is exactly 0
 * (unlike binary where dropped bits bias toward +0.5). Therefore:
 *   - The error is symmetric around 0
 *   - The maximum absolute error < 0.5 ulp
 *   - No compensation constant is needed
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_TRUNC_MUL_H
#define SET6_TRIT_TRUNC_MUL_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define TMUL_MAX_TRITS     32   /**< Max operand width in trits           */
#define TMUL_FP_SCALE      1000 /**< Fixed-point scale ×1000              */
#define TMUL_AREA_SAVE_PCT 220  /**< Area savings ×10 = 22.0%             */

/* ==== Structures ======================================================== */

/**
 * @brief Truncated multiplier state.
 */
typedef struct {
    int  initialized;
    int  operand_trits;     /**< Width of operands in trits             */
    int  truncate_trits;    /**< Number of low trits to truncate        */
    int  total_muls;        /**< Total multiplications performed        */
    int  max_error_x1000;   /**< Max observed |error| in ulp ×1000     */
    int  avg_error_x1000;   /**< Running average |error| in ulp ×1000  */
    int64_t error_sum;      /**< Sum of all absolute errors (for avg)   */
} tmul_state_t;

/* ==== API ============================================================== */

/**
 * @brief Initialize truncated multiplier.
 * @param st             State to initialize.
 * @param operand_trits  Width of each operand in trits.
 * @param truncate_trits Number of low trits to chop from partial products.
 * @return 0 on success, -1 on error.
 */
int tmul_init(tmul_state_t *st, int operand_trits, int truncate_trits);

/**
 * @brief Full (exact) balanced ternary multiplication.
 * @param a  First operand (integer value in balanced ternary range).
 * @param b  Second operand.
 * @return Exact product.
 */
int64_t tmul_full(int a, int b);

/**
 * @brief Truncated balanced ternary multiplication.
 *
 * Drops the lowest `truncate_trits` partial products columns.
 * Error < 0.5 ulp due to balanced ternary symmetry.
 *
 * @param st  State (updated with error statistics).
 * @param a   First operand.
 * @param b   Second operand.
 * @return Truncated product.
 */
int64_t tmul_truncated(tmul_state_t *st, int a, int b);

/**
 * @brief Compute truncation error between full and truncated results.
 * @param full_product  Exact product.
 * @param trunc_product Truncated product.
 * @return Absolute error (non-negative).
 */
int tmul_error(int64_t full_product, int64_t trunc_product);

/**
 * @brief Compute area savings ×10 for current truncation setting.
 *
 * Area ∝ n² for full multiplier, (n-k)² + correction for truncated.
 * Savings ≈ (2nk - k²) / n² × 1000.
 *
 * @param st  State.
 * @return Area savings in per-mille (e.g., 220 = 22.0%).
 */
int tmul_area_savings(const tmul_state_t *st);

/**
 * @brief Get maximum observed error in ulp ×1000.
 * @param st  State.
 * @return Max error ×1000 (should be < 500 for balanced ternary).
 */
int tmul_max_error(const tmul_state_t *st);

/**
 * @brief Get average observed error in ulp ×1000.
 * @param st  State.
 * @return Average error ×1000.
 */
int tmul_avg_error(const tmul_state_t *st);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_TRUNC_MUL_H */
