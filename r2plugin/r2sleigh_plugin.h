/* r2sleigh plugin shared declarations */

#ifndef R2SLEIGH_PLUGIN_H
#define R2SLEIGH_PLUGIN_H

#include <r_anal.h>
#include "r2sleigh_api_v2.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Function declarations shared between plugins */
R2ILContext *get_context(RAnal *anal);
void r2sleigh_set_arch_override(const char *arch);
/* The single machine-evidence -> Sleigh language mapping. NULL means refuse:
 * no bundled language matches the binary's headers. */
const char *r2sleigh_language_for_bin_info(RBinInfo *info);
int sleigh_op(RAnal *anal, RAnalOp *op, ut64 addr, const ut8 *data, int len, int mask);

#ifdef __cplusplus
}
#endif

#endif /* R2SLEIGH_PLUGIN_H */
