/* radare2 - LGPL - Copyright 2025 - r2sleigh project */

#include <r_arch.h>
#include <r_anal.h>
#include <r_core.h>
#include <r_version.h>
#include <stdlib.h>
#include <string.h>
#include "r2sleigh_plugin.h"

/* Lift-core support is a capability of the loaded r2sleigh library, not a
 * property of radare2's ABI number. */

static const char *fallback_profile_generic(void) {
	return "gpr\tpc\t.64\t0\t0\n\
gpr\tsp\t.64\t8\t0\n\
gpr\ta0\t.64\t16\t0\n\
=PC\tpc\n\
=SP\tsp\n\
=A0\ta0\n";
}

static const char *fallback_profile_x86_64(void) {
	return "gpr\trax\t.64\t0\t0\n\
gpr\trbx\t.64\t1\t0\n\
gpr\trcx\t.64\t2\t0\n\
gpr\trdx\t.64\t3\t0\n\
gpr\trsi\t.64\t4\t0\n\
gpr\trdi\t.64\t5\t0\n\
gpr\tr8\t.64\t6\t0\n\
gpr\tr9\t.64\t7\t0\n\
gpr\tr10\t.64\t8\t0\n\
gpr\tr11\t.64\t9\t0\n\
gpr\tr12\t.64\t10\t0\n\
gpr\tr13\t.64\t11\t0\n\
gpr\tr14\t.64\t12\t0\n\
gpr\tr15\t.64\t13\t0\n\
gpr\trsp\t.64\t14\t0\n\
gpr\trbp\t.64\t15\t0\n\
gpr\trip\t.64\t16\t0\n\
gpr\teax\t.32\t0\t0\n\
gpr\tecx\t.32\t2\t0\n\
gpr\tedx\t.32\t3\t0\n\
gpr\tesi\t.32\t4\t0\n\
gpr\tedi\t.32\t5\t0\n\
gpr\tal\t.8\t0\t0\n\
gpr\tzf\t.1\t17\t0\n\
gpr\tcf\t.1\t18\t0\n\
gpr\tsf\t.1\t19\t0\n\
gpr\tof\t.1\t20\t0\n\
=PC\trip\n\
=SP\trsp\n\
=BP\trbp\n\
=R0\trax\n\
=A0\trdi\n\
=A1\trsi\n\
=A2\trdx\n\
=A3\trcx\n\
=CF\tcf\n\
=ZF\tzf\n\
=SF\tsf\n\
=OF\tof\n";
}

static const char *fallback_profile_arm64(void) {
	return "gpr\tx0\t.64\t0\t0\n\
gpr\tx1\t.64\t8\t0\n\
gpr\tx2\t.64\t16\t0\n\
gpr\tx3\t.64\t24\t0\n\
gpr\tx8\t.64\t64\t0\n\
gpr\tx16\t.64\t128\t0\n\
gpr\tx29\t.64\t232\t0\n\
gpr\tsp\t.64\t248\t0\n\
gpr\tpc\t.64\t256\t0\n\
gpr\tcf\t.1\t280\t0\n\
gpr\tzf\t.1\t281\t0\n\
gpr\tnf\t.1\t282\t0\n\
gpr\tvf\t.1\t283\t0\n\
=PC\tpc\n\
=SP\tsp\n\
=BP\tx29\n\
=R0\tx0\n\
=R1\tx1\n\
=R2\tx2\n\
=R3\tx3\n\
=A0\tx0\n\
=A1\tx1\n\
=A2\tx2\n\
=A3\tx3\n\
=SN\tx16\n\
=CF\tcf\n\
=ZF\tzf\n\
=SF\tnf\n\
=OF\tvf\n";
}

static const char *sleigh_fallback_profile(RAnal *anal) {
	if (!anal || !anal->config || !anal->config->arch[0]) {
		return fallback_profile_generic ();
	}
	const char *arch = anal->config->arch;
	const int bits = anal->config->bits;
	if (!strcmp (arch, "arm64") || !strcmp (arch, "aarch64")
		|| (!strcmp (arch, "arm") && bits == 64)) {
		return fallback_profile_arm64 ();
	}
	if (!strcmp (arch, "x86")) {
		return fallback_profile_x86_64 ();
	}
	return fallback_profile_generic ();
}

static RAnal *sleigh_arch_anal(RArchSession *as) {
	RCore *core = as? (RCore *)as->user: NULL;
	return core? core->anal: NULL;
}

/* One mapping, shared with the anal plugin: see sleigh_language_for_machine in
 * r_anal_sleigh.c. Two copies of this decision used to disagree about
 * endianness and CPU variants. */
static const char *sleigh_arch_name(RArchSession *as) {
	RCore *core = as? (RCore *)as->user: NULL;
	return r2sleigh_language_for_bin_info (core? r_bin_get_info (core->bin): NULL);
}

static RAnal *sleigh_arch_prepare(RArchSession *as) {
	const char *arch = sleigh_arch_name (as);
	if (arch) {
		r2sleigh_set_arch_override (arch);
	}
	return sleigh_arch_anal (as);
}

static char *sleigh_arch_regs(RArchSession *as) {
	RAnal *anal = sleigh_arch_prepare (as);
	const char *fallback = sleigh_fallback_profile (anal);
	if (!anal) {
		return strdup (fallback);
	}

	/* Try to get register profile from r2sleigh context */
	R2ILContext *ctx = get_context (anal);
	if (!ctx) {
		return strdup (fallback);
	}

	const R2SleighApiV2 *api = r2sleigh_api_v2 ();
	if (!api || api->abi_version != R2SLEIGH_ABI_V2
		|| api->struct_size != sizeof (*api)
		|| !(api->capabilities & R2SLEIGH_CAP_OPAQUE_RADARE_SNAPSHOT_V2)
		|| api->byte_view_size != sizeof (R2SleighByteViewV2)
		|| api->string_view_size != sizeof (R2SleighStringViewV2)
		|| !(api->capabilities & R2SLEIGH_CAP_LIFT_CORE_V2)
		|| !api->lift_context_reg_profile
		|| !api->owned_bytes_view || !api->owned_bytes_free) {
		return strdup (fallback);
	}

	R2SleighOwnedBytesV2 *profile = NULL;
	if (api->lift_context_reg_profile (ctx, &profile) != R2SLEIGH_STATUS_OK_V2
		|| !profile) {
		return strdup (fallback);
	}
	R2SleighByteViewV2 view = {0};
	char *copy = NULL;
	uint32_t view_status = api->owned_bytes_view (profile, &view);
	if (view_status == R2SLEIGH_STATUS_OK_V2
		&& (!view.len || view.data) && view.len != SIZE_MAX) {
		copy = malloc (view.len + 1);
		if (copy) {
			if (view.len) {
				memcpy (copy, view.data, view.len);
			}
			copy[view.len] = '\0';
		}
	}
	uint32_t free_status = api->owned_bytes_free (profile);
	if (view_status != R2SLEIGH_STATUS_OK_V2 || free_status != R2SLEIGH_STATUS_OK_V2) {
		free (copy);
		copy = NULL;
	}
	return copy ? copy : strdup (fallback);
}

static bool sleigh_arch_decode(RArchSession *as, RAnalOp *op, RArchDecodeMask mask) {
	RAnal *anal = sleigh_arch_prepare (as);
	if (!anal) {
		return false;
	}

	/* Use our existing sleigh_op function */
	return sleigh_op (anal, op, op->addr, op->bytes, op->size, mask) >= 0;
}

static int sleigh_arch_info(RArchSession *as, ut32 query) {
	RAnal *anal = sleigh_arch_prepare (as);
	if (!anal) {
		return 0;
	}

	R2ILContext *ctx = get_context (anal);
	if (!ctx) {
		return 0;
	}

	switch (query) {
	case R_ARCH_INFO_MINOP_SIZE:
		return 1;
	case R_ARCH_INFO_MAXOP_SIZE:
		return 15;
	case R_ARCH_INFO_CODE_ALIGN:
		return 1;
	case R_ARCH_INFO_DATA_ALIGN:
		return 1;
	case R_ARCH_INFO_FUNC_ALIGN:
		return 1;
	default:
		return 0;
	}
}

/* Define architecture plugins for different variants */
RArchPlugin r_arch_plugin_sleigh_x86 = {
	.meta = {
		.name = "r2sleigh",
		.author = "r2sleigh project",
		.desc = "Sleigh-based architecture via r2sleigh (P-code to ESIL)",
		.license = "LGPL3",
	},
	.arch = "r2sleigh",
	.bits = R_SYS_BITS_PACK1 (32) | R_SYS_BITS_PACK1 (64),
	.decode = sleigh_arch_decode,
	.info = sleigh_arch_info,
	.regs = sleigh_arch_regs,
};

#ifndef R2_PLUGIN_INCORE
R_API RLibStruct radare_plugin = {
	.type = R_LIB_TYPE_ARCH,
	.data = &r_arch_plugin_sleigh_x86,
	.version = R2_VERSION,
	.abiversion = R2_ABIVERSION
};
#endif
