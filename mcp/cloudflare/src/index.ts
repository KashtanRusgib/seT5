/**
 * seT5/seT6 Ternary Microkernel — Cloudflare Workers MCP Server
 *
 * Exposes project documentation, architecture, test inventories,
 * and reference data as MCP tools over Server-Sent Events (SSE).
 *
 * Endpoint: https://<worker>.workers.dev/sse
 *
 * NOTE: Because the C toolchain cannot run inside V8 isolates,
 * this server provides read-only reference tools. For build/test
 * execution, use the Cloud Run or Local STDIO deployments.
 *
 * Security: Set `API_KEY` secret via `wrangler secret put API_KEY`
 * to require an X-API-Key header on all requests.
 */

import { McpAgent } from "agents/mcp";
import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { z } from "zod";

// ── Embedded reference data ─────────────────────────────────────────

const ARCHITECTURE_SUMMARY = `
seT5 is a ground-up rewrite of the seL4 verified microkernel using balanced ternary logic (Kleene K₃).
- 3 trit-values: T (true/+1), F (false/−1), U (unknown/0)
- Hardware targets: CNTFET, STT-MRAM, memristive crossbar
- Formal verification: Isabelle/HOL proofs for all core invariants
- Test suite: 66+ active suites, 5280+ runtime assertions, 0 failures
- Build system: GNU Make + custom ternary C compiler
- Python bindings: Trithon (numpy-backed balanced ternary operations)
`.trim();

const TEST_SUITES = [
    "test_adversarial", "test_ai_acceleration", "test_art9",
    "test_binary_sentinel", "test_dlt_cntfet", "test_fault_tolerant_network",
    "test_friday_updates", "test_functional_utility", "test_godel_machine",
    "test_hardening", "test_huawei_cn119652311a", "test_hybrid_ai",
    "test_ingole_wo2016199157a1", "test_integration", "test_ipc_secure",
    "test_memory_safety", "test_mixed_radix_bos", "test_modular",
    "test_multi_radix_unit", "test_papers", "test_papers2",
    "test_peirce_semiotic", "test_red_team_binary_reversion",
    "test_red_team_crypto", "test_red_team_crypto_net_security",
    "test_red_team_deep", "test_red_team_fullstack_kernel",
    "test_red_team_godel", "test_red_team_lego_namespace_collision",
    "test_red_team_packed_hardened", "test_red_team_resource_exhaustion",
    "test_red_team_simd", "test_red_team_symbiotic",
    "test_red_team_trit_linux_ipc_net", "test_red_team_trit_range",
    "test_red_team_type", "test_rns", "test_samsung_cn105745888a",
    "test_samsung_cn105745888a_correlator", "test_samsung_us11170290b2",
    "test_scheduler_concurrency", "test_sel4_ternary", "test_sigma9",
    "test_sigma9_mcp", "test_stress", "test_symbiotic_ai",
    "test_symbiotic_beauty", "test_symbiotic_curiosity",
    "test_symbiotic_eudaimonia", "test_tbe", "test_ternary_compiler_integration",
    "test_ternary_database", "test_ternary_formal_suite",
    "test_ternary_full_adder", "test_ternary_pdfs",
    "test_ternary_reversion_guard", "test_ternary_sense_amp",
    "test_ternary_wallace_tree", "test_time", "test_tipc_compressor",
    "test_trilang", "test_trit_linux", "test_trit_simd_regression",
    "test_tsmc_tmd_intel_pam3_hynix_tcam",
];

const KERNEL_MODULES = [
    { name: "init.c", desc: "Kernel initialization and boot sequence" },
    { name: "memory.c", desc: "Ternary memory management (3-state pages)" },
    { name: "ipc.c", desc: "Inter-process communication (balanced ternary IPC)" },
    { name: "scheduler.c", desc: "Process scheduler with ternary priority levels" },
    { name: "syscall.c", desc: "System call interface" },
    { name: "multiradix.c", desc: "Mixed-radix arithmetic operations" },
    { name: "trit_crypto.c", desc: "Ternary cryptographic primitives" },
    { name: "srbc.c", desc: "Self-Repairing Balanced Code (ECC)" },
    { name: "radix_transcode.c", desc: "Radix-2 ↔ radix-3 transcoding" },
    { name: "stt_mram.c", desc: "STT-MRAM ternary memory controller" },
    { name: "tipc.c", desc: "Ternary IPC protocol (TIPC)" },
    { name: "tfs.c", desc: "Ternary File System" },
];

const BALANCED_TERNARY_REFERENCE = `
Balanced Ternary Quick Reference (Kleene K₃):
  Values: T (+1), U (0), F (−1)

  NOT (unary):  NOT T = F,  NOT U = U,  NOT F = T
  AND:  T∧T=T, T∧U=U, T∧F=F, U∧U=U, U∧F=F, F∧F=F
  OR:   T∨T=T, T∨U=T, T∨F=T, U∨U=U, U∨F=U, F∨F=F

  Ternary addition (digit-level, carry-propagate):
    T+T = F carry T    T+U = T    T+F = U
    U+U = U            U+F = F
    F+F = T carry F

  Representation: A balanced ternary integer N = Σ aᵢ · 3ⁱ  where aᵢ ∈ {−1, 0, +1}
`.trim();

// ── Type for the environment bindings ───────────────────────────────

type Env = {
    API_KEY?: string;
};

// ── MCP Agent ───────────────────────────────────────────────────────

export class SeT5McpAgent extends McpAgent<Env> {
    server = new McpServer({
        name: "seT5-mcp",
        version: "1.0.0",
    });

    async init() {
        // ── Tool: get_architecture ───────────────────────────────────
        this.server.tool(
            "get_architecture",
            "Get the seT5/seT6 ternary microkernel architecture summary",
            {},
            async () => ({
                content: [{ type: "text", text: ARCHITECTURE_SUMMARY }],
            })
        );

        // ── Tool: list_test_suites ──────────────────────────────────
        this.server.tool(
            "list_test_suites",
            "List all 66+ test suites in the seT5 verification suite",
            {},
            async () => ({
                content: [
                    {
                        type: "text",
                        text: `${TEST_SUITES.length} test suites:\n${TEST_SUITES.map((s) => `  • ${s}`).join("\n")}`,
                    },
                ],
            })
        );

        // ── Tool: list_kernel_modules ───────────────────────────────
        this.server.tool(
            "list_kernel_modules",
            "List the core kernel source modules and their purposes",
            {},
            async () => ({
                content: [
                    {
                        type: "text",
                        text: KERNEL_MODULES.map(
                            (m) => `${m.name}: ${m.desc}`
                        ).join("\n"),
                    },
                ],
            })
        );

        // ── Tool: balanced_ternary_reference ────────────────────────
        this.server.tool(
            "balanced_ternary_reference",
            "Get balanced ternary (Kleene K₃) logic truth tables and arithmetic reference",
            {},
            async () => ({
                content: [{ type: "text", text: BALANCED_TERNARY_REFERENCE }],
            })
        );

        // ── Tool: search_test_suites ────────────────────────────────
        this.server.tool(
            "search_test_suites",
            "Search test suites by keyword (e.g., 'red_team', 'samsung', 'crypto')",
            { query: z.string().describe("Keyword to search for in test suite names") },
            async ({ query }) => {
                const q = query.toLowerCase();
                const matches = TEST_SUITES.filter((s) =>
                    s.toLowerCase().includes(q)
                );
                return {
                    content: [
                        {
                            type: "text",
                            text: matches.length > 0
                                ? `Found ${matches.length} matching suites:\n${matches.map((s) => `  • ${s}`).join("\n")}`
                                : `No test suites matching "${query}"`,
                        },
                    ],
                };
            }
        );

        // ── Tool: get_deployment_info ───────────────────────────────
        this.server.tool(
            "get_deployment_info",
            "Get deployment options and status for the seT5 MCP server",
            {},
            async () => ({
                content: [
                    {
                        type: "text",
                        text: [
                            "seT5 MCP Server — Deployment Options:",
                            "",
                            "1. Local (STDIO)  — Full build/test capabilities via Python MCP SDK",
                            "   cd mcp/local && pip install -r requirements.txt && python server.py",
                            "",
                            "2. Cloudflare Workers (SSE) — Read-only reference tools (this server)",
                            "   cd mcp/cloudflare && npm install && npm run deploy",
                            "   Endpoint: https://<worker>.workers.dev/sse",
                            "",
                            "3. Google Cloud Run (HTTP+SSE) — Full build/test in Docker container",
                            "   cd mcp/cloudrun && gcloud run deploy --source .",
                            "",
                            "Current: Cloudflare Workers (read-only reference mode)",
                            "For build/test execution, use Local STDIO or Cloud Run.",
                        ].join("\n"),
                    },
                ],
            })
        );
    }
}

// ── Request handler with optional API key check ─────────────────────

export default {
    async fetch(request: Request, env: Env, ctx: ExecutionContext): Promise<Response> {
        const url = new URL(request.url);

        // Health check
        if (url.pathname === "/" || url.pathname === "/health") {
            return new Response(
                JSON.stringify({
                    status: "ok",
                    server: "seT5-mcp",
                    version: "1.0.0",
                    transport: "sse",
                    endpoint: "/sse",
                }),
                { headers: { "Content-Type": "application/json" } }
            );
        }

        // Optional API key check (set via `wrangler secret put API_KEY`)
        if (env.API_KEY) {
            const provided = request.headers.get("X-API-Key") ?? url.searchParams.get("api_key");
            if (provided !== env.API_KEY) {
                return new Response(
                    JSON.stringify({ error: "Unauthorized", hint: "Set X-API-Key header" }),
                    { status: 401, headers: { "Content-Type": "application/json" } }
                );
            }
        }

        // Delegate to MCP agent for /sse and /mcp paths
        return SeT5McpAgent.mount("/sse").fetch(request, env, ctx);
    },
};
