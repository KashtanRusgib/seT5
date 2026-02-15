/*
 * linker.c - Ternary Bytecode Linker Implementation (Phase 3)
 *
 * Links multiple compiled object modules into a single executable
 * by resolving cross-module symbol references and patching CALL
 * targets with final addresses.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../include/linker.h"
#include "../include/logger.h"

void linker_init(Linker *lnk) {
    memset(lnk, 0, sizeof(Linker));
}

int linker_add_module(Linker *lnk, const unsigned char *code, int code_len) {
    if (lnk->module_count >= LINK_MAX_MODULES) {
        if (lnk->error_count < 16) {
            snprintf(lnk->errors[lnk->error_count++], 128,
                     "too many modules (max %d)", LINK_MAX_MODULES);
        }
        return -1;
    }
    if (code_len > LINK_MAX_CODE) {
        if (lnk->error_count < 16) {
            snprintf(lnk->errors[lnk->error_count++], 128,
                     "module code too large (%d bytes, max %d)", code_len, LINK_MAX_CODE);
        }
        return -1;
    }

    int id = lnk->module_count++;
    ObjectModule *mod = &lnk->modules[id];
    mod->id = id;
    memcpy(mod->code, code, (size_t)code_len);
    mod->code_len = code_len;
    mod->sym_count = 0;
    mod->reloc_count = 0;
    mod->base_addr = 0;

    return id;
}

int linker_add_symbol(Linker *lnk, int module_id, const char *name,
                      int address, SymVisibility vis) {
    if (module_id < 0 || module_id >= lnk->module_count) return -1;
    ObjectModule *mod = &lnk->modules[module_id];
    if (mod->sym_count >= LINK_MAX_SYMBOLS) return -1;

    LinkSymbol *sym = &mod->symbols[mod->sym_count++];
    strncpy(sym->name, name, 63);
    sym->name[63] = '\0';
    sym->address = address;
    sym->module_id = module_id;
    sym->vis = vis;

    return 0;
}

int linker_add_reloc(Linker *lnk, int module_id, int offset,
                     const char *target_name) {
    if (module_id < 0 || module_id >= lnk->module_count) return -1;
    ObjectModule *mod = &lnk->modules[module_id];
    if (mod->reloc_count >= LINK_MAX_RELOCS) return -1;

    Relocation *rel = &mod->relocs[mod->reloc_count++];
    rel->offset = offset;
    strncpy(rel->target_name, target_name, 63);
    rel->target_name[63] = '\0';
    rel->module_id = module_id;

    return 0;
}

int linker_resolve(const Linker *lnk, const char *name) {
    for (int i = 0; i < lnk->global_count; i++) {
        if (strcmp(lnk->globals[i].name, name) == 0) {
            return lnk->globals[i].address;
        }
    }
    return -1;
}

int linker_link(Linker *lnk) {
    LOG_INFO_MSG("Linker", "TASK-029", "linker_link entered");

    /* Phase 1: Assign base addresses (concatenate modules) */
    int base = 0;
    for (int m = 0; m < lnk->module_count; m++) {
        lnk->modules[m].base_addr = base;
        base += lnk->modules[m].code_len;
    }

    if (base > LINK_MAX_CODE) {
        if (lnk->error_count < 16) {
            snprintf(lnk->errors[lnk->error_count++], 128,
                     "linked output too large (%d bytes, max %d)", base, LINK_MAX_CODE);
        }
        return lnk->error_count;
    }

    /* Phase 2: Collect global symbols (exports) */
    lnk->global_count = 0;
    for (int m = 0; m < lnk->module_count; m++) {
        ObjectModule *mod = &lnk->modules[m];
        for (int s = 0; s < mod->sym_count; s++) {
            LinkSymbol *sym = &mod->symbols[s];
            if (sym->vis == SYM_EXPORT) {
                /* Check for duplicates */
                int dup = 0;
                for (int g = 0; g < lnk->global_count; g++) {
                    if (strcmp(lnk->globals[g].name, sym->name) == 0) {
                        if (lnk->error_count < 16) {
                            snprintf(lnk->errors[lnk->error_count++], 128,
                                     "duplicate symbol '%s' (modules %d and %d)",
                                     sym->name, lnk->globals[g].module_id, m);
                        }
                        dup = 1;
                        break;
                    }
                }
                if (!dup && lnk->global_count < LINK_MAX_SYMBOLS) {
                    LinkSymbol *g = &lnk->globals[lnk->global_count++];
                    strncpy(g->name, sym->name, 63);
                    g->name[63] = '\0';
                    g->address = sym->address + mod->base_addr; /* Relocated */
                    g->module_id = m;
                    g->vis = SYM_EXPORT;
                }
            }
        }
    }

    /* Phase 3: Copy code to output buffer */
    lnk->output_len = 0;
    for (int m = 0; m < lnk->module_count; m++) {
        ObjectModule *mod = &lnk->modules[m];
        memcpy(lnk->output + mod->base_addr, mod->code, (size_t)mod->code_len);
        lnk->output_len += mod->code_len;
    }

    /* Phase 4: Resolve relocations */
    for (int m = 0; m < lnk->module_count; m++) {
        ObjectModule *mod = &lnk->modules[m];
        for (int r = 0; r < mod->reloc_count; r++) {
            Relocation *rel = &mod->relocs[r];
            int resolved_addr = linker_resolve(lnk, rel->target_name);
            if (resolved_addr < 0) {
                /* Check if it's a local symbol */
                int found = 0;
                for (int s = 0; s < mod->sym_count; s++) {
                    if (strcmp(mod->symbols[s].name, rel->target_name) == 0) {
                        resolved_addr = mod->symbols[s].address + mod->base_addr;
                        found = 1;
                        break;
                    }
                }
                if (!found) {
                    if (lnk->error_count < 16) {
                        snprintf(lnk->errors[lnk->error_count++], 128,
                                 "undefined symbol '%s' referenced in module %d",
                                 rel->target_name, m);
                    }
                    continue;
                }
            }

            /* Patch the byte at the relocation offset */
            int abs_offset = rel->offset + mod->base_addr;
            if (abs_offset >= 0 && abs_offset < lnk->output_len) {
                lnk->output[abs_offset] = (unsigned char)(resolved_addr & 0xFF);
            }
        }
    }

    /* Phase 5: Check for unresolved imports */
    for (int m = 0; m < lnk->module_count; m++) {
        ObjectModule *mod = &lnk->modules[m];
        for (int s = 0; s < mod->sym_count; s++) {
            if (mod->symbols[s].vis == SYM_IMPORT) {
                if (linker_resolve(lnk, mod->symbols[s].name) < 0) {
                    if (lnk->error_count < 16) {
                        snprintf(lnk->errors[lnk->error_count++], 128,
                                 "unresolved import '%s' in module %d",
                                 mod->symbols[s].name, m);
                    }
                }
            }
        }
    }

    LOG_INFO_MSG("Linker", "TASK-029", "linker_link complete");
    return lnk->error_count;
}

void linker_report_errors(const Linker *lnk) {
    if (lnk->error_count == 0) return;
    fprintf(stderr, "=== Linker Errors (%d) ===\n", lnk->error_count);
    for (int i = 0; i < lnk->error_count; i++) {
        fprintf(stderr, "  [%d] %s\n", i + 1, lnk->errors[i]);
    }
}
