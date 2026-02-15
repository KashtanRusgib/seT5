/**
 * @file dev_trit.h
 * @brief /dev/trit — Ternary Character Device Driver Stub
 *
 * Provides a virtual character device interface for userspace access
 * to balanced ternary hardware registers:
 *
 *   /dev/trit   — read/write ternary trits (scalar or register)
 *   ioctl:
 *     TRIT_IOCTL_GET_REG   — read a 32-trit register
 *     TRIT_IOCTL_SET_REG   — write a 32-trit register
 *     TRIT_IOCTL_DOT       — execute DOT_TRIT instruction
 *     TRIT_IOCTL_FFT       — execute FFT_STEP
 *     TRIT_IOCTL_NOISE_CFG — configure QEMU noise model
 *     TRIT_IOCTL_WCET_Q    — query WCET telemetry
 *
 * This is a stub for development. On real hardware, this would
 * interface with memory-mapped ternary ALU registers.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_DEV_TRIT_H
#define SET5_DEV_TRIT_H

#include "set5/trit.h"
#include "set5/trit_emu.h"
#include "set5/multiradix.h"
#include "set5/qemu_trit.h"
#include "set5/wcet.h"

/* ---- ioctl command numbers -------------------------------------------- */

#define TRIT_IOC_MAGIC  'T'

#define TRIT_IOCTL_GET_REG    ((TRIT_IOC_MAGIC << 8) | 0x01)
#define TRIT_IOCTL_SET_REG    ((TRIT_IOC_MAGIC << 8) | 0x02)
#define TRIT_IOCTL_DOT        ((TRIT_IOC_MAGIC << 8) | 0x03)
#define TRIT_IOCTL_FFT        ((TRIT_IOC_MAGIC << 8) | 0x04)
#define TRIT_IOCTL_RADIX_CONV ((TRIT_IOC_MAGIC << 8) | 0x05)
#define TRIT_IOCTL_NOISE_CFG  ((TRIT_IOC_MAGIC << 8) | 0x10)
#define TRIT_IOCTL_NOISE_STAT ((TRIT_IOC_MAGIC << 8) | 0x11)
#define TRIT_IOCTL_WCET_Q     ((TRIT_IOC_MAGIC << 8) | 0x20)
#define TRIT_IOCTL_TELEMETRY  ((TRIT_IOC_MAGIC << 8) | 0x21)

/* ---- ioctl argument structures ---------------------------------------- */

typedef struct {
    int            reg_index;      /* Register number (0-15) */
    trit2_reg32    reg_value;      /* Register contents */
} trit_ioctl_reg_t;

typedef struct {
    int            reg_a;          /* Source register A */
    int            reg_b;          /* Source register B */
    int            result;         /* Scalar dot product result */
} trit_ioctl_dot_t;

typedef struct {
    int            reg_index;      /* Register to butterfly */
    int            offset;         /* Trit offset within register */
} trit_ioctl_fft_t;

typedef struct {
    int            reg_index;      /* Target register */
    int            binary_value;   /* Binary integer to convert */
} trit_ioctl_radix_t;

typedef struct {
    int            model;          /* noise_model_t enum value */
    int            seed;           /* PRNG seed */
    int            prob_ppm;       /* Flip probability in ppm */
} trit_ioctl_noise_cfg_t;

typedef struct {
    int            total_reads;
    int            faults_injected;
    int            faults_cosmic;
    int            drift_cycles;
} trit_ioctl_noise_stat_t;

typedef struct {
    int            probe_id;       /* WCET probe index */
    int            budget;         /* Cycle budget */
    int            observed_max;   /* Worst observed */
    int            violations;     /* Violation count */
    int            average_x100;   /* Average * 100 (fixed point) */
} trit_ioctl_wcet_t;

typedef struct {
    int            lb_total_insns;
    int            lb_trit_insns;
    int            lb_core_affinity; /* -1=binary, 0=any, 1=trit */
} trit_ioctl_telemetry_t;

/* ---- Device State ----------------------------------------------------- */

typedef struct {
    multiradix_state_t  mr;       /* Multi-radix register file */
    qemu_noise_t        noise;    /* Noise simulator */
    wcet_state_t        wcet;     /* WCET probes */
    int                 open;     /* Device is open */
} dev_trit_state_t;

/* ---- Device Operations ------------------------------------------------ */

/**
 * @brief Open /dev/trit.
 */
static inline int dev_trit_open(dev_trit_state_t *dev) {
    if (!dev) return -1;
    multiradix_init(&dev->mr);
    qemu_noise_init(&dev->noise, NOISE_NONE, 0, 0);
    wcet_init(&dev->wcet);
    dev->open = 1;
    return 0;
}

/**
 * @brief Close /dev/trit.
 */
static inline int dev_trit_close(dev_trit_state_t *dev) {
    if (!dev) return -1;
    dev->open = 0;
    return 0;
}

/**
 * @brief Read a single trit (character device read).
 *
 * Reads from register 0, position 0 by default.
 * Returns the decoded trit value as a byte: 0xFF=-1, 0x00=0, 0x01=1
 */
static inline int dev_trit_read(dev_trit_state_t *dev) {
    if (!dev || !dev->open) return -1;
    trit2 t = trit2_reg32_get(&dev->mr.regs[0], 0);

    /* Apply noise if enabled */
    int decoded = trit2_decode(t);
    trit noisy = qemu_noise_read(&dev->noise, trit_from_int(decoded));
    return (int)noisy;
}

/**
 * @brief Write a single trit.
 *
 * Writes to register 0, position 0 by default.
 */
static inline int dev_trit_write(dev_trit_state_t *dev, int value) {
    if (!dev || !dev->open) return -1;
    if (value < -1 || value > 1) return -22; /* EINVAL */
    trit t = trit_from_int(value);
    trit2 packed = trit_to_trit2(t);
    trit2_reg32_set(&dev->mr.regs[0], 0, packed);
    return 0;
}

/**
 * @brief ioctl dispatch for /dev/trit.
 */
static inline int dev_trit_ioctl(dev_trit_state_t *dev, int cmd, void *arg) {
    if (!dev || !dev->open) return -1;

    switch (cmd) {
    case TRIT_IOCTL_GET_REG: {
        trit_ioctl_reg_t *r = (trit_ioctl_reg_t *)arg;
        if (!r || r->reg_index < 0 || r->reg_index >= MR_NUM_REGS) return -22;
        r->reg_value = dev->mr.regs[r->reg_index];
        return 0;
    }
    case TRIT_IOCTL_SET_REG: {
        trit_ioctl_reg_t *r = (trit_ioctl_reg_t *)arg;
        if (!r || r->reg_index < 0 || r->reg_index >= MR_NUM_REGS) return -22;
        dev->mr.regs[r->reg_index] = r->reg_value;
        return 0;
    }
    case TRIT_IOCTL_DOT: {
        trit_ioctl_dot_t *d = (trit_ioctl_dot_t *)arg;
        if (!d) return -22;
        d->result = dot_trit(&dev->mr, d->reg_a, d->reg_b);
        return 0;
    }
    case TRIT_IOCTL_FFT: {
        trit_ioctl_fft_t *f = (trit_ioctl_fft_t *)arg;
        if (!f) return -22;
        fft_step(&dev->mr, f->reg_index, f->offset, 1);
        return 0;
    }
    case TRIT_IOCTL_RADIX_CONV: {
        trit_ioctl_radix_t *r = (trit_ioctl_radix_t *)arg;
        if (!r) return -22;
        radix_conv_to_ternary(&dev->mr, r->reg_index, r->binary_value);
        return 0;
    }
    case TRIT_IOCTL_NOISE_CFG: {
        trit_ioctl_noise_cfg_t *n = (trit_ioctl_noise_cfg_t *)arg;
        if (!n) return -22;
        qemu_noise_init(&dev->noise, (noise_model_t)n->model,
                         n->seed, n->prob_ppm);
        return 0;
    }
    case TRIT_IOCTL_NOISE_STAT: {
        trit_ioctl_noise_stat_t *s = (trit_ioctl_noise_stat_t *)arg;
        if (!s) return -22;
        s->total_reads     = dev->noise.total_reads;
        s->faults_injected = dev->noise.faults_injected;
        s->faults_cosmic   = dev->noise.faults_cosmic;
        s->drift_cycles    = dev->noise.drift_cycles;
        return 0;
    }
    case TRIT_IOCTL_WCET_Q: {
        trit_ioctl_wcet_t *w = (trit_ioctl_wcet_t *)arg;
        if (!w || w->probe_id < 0 || w->probe_id >= (int)dev->wcet.probe_count)
            return -22;
        wcet_probe_t *p = &dev->wcet.probes[w->probe_id];
        w->budget       = (int)p->budget_cycles;
        w->observed_max = (int)p->observed_max;
        w->violations   = p->violation_count;
        w->average_x100 = (p->invocation_count > 0) ? (int)(p->observed_sum * 100 / p->invocation_count) : 0;
        return 0;
    }
    case TRIT_IOCTL_TELEMETRY: {
        trit_ioctl_telemetry_t *t = (trit_ioctl_telemetry_t *)arg;
        if (!t) return -22;
        trit_lb_snapshot_t ss = trit_lb_snapshot(&dev->mr);
        t->lb_total_insns   = ss.total_insns;
        t->lb_trit_insns    = ss.trit_ratio_pct;
        t->lb_core_affinity = ss.suggested_affinity;
        return 0;
    }
    default:
        return -25; /* ENOTTY — invalid ioctl */
    }
}

#endif /* SET5_DEV_TRIT_H */
