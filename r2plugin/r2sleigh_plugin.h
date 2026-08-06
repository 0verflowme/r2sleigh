/* r2sleigh plugin shared declarations */

#ifndef R2SLEIGH_PLUGIN_H
#define R2SLEIGH_PLUGIN_H

#include <r_anal.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Forward declaration of R2ILContext */
typedef struct R2ILContext R2ILContext;

/* Function declarations shared between plugins */
R2ILContext *get_context(RAnal *anal);
void r2sleigh_set_arch_override(const char *arch);
char *r2il_get_reg_profile(R2ILContext *ctx);
int sleigh_op(RAnal *anal, RAnalOp *op, ut64 addr, const ut8 *data, int len, int mask);

#ifdef __cplusplus
}
#endif

#endif /* R2SLEIGH_PLUGIN_H */
