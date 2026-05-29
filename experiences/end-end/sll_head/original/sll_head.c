#include "../QualifiedCProgramming/QCP_examples/QCP_demos_LLM/sll_def.h"

int sll_head(struct list *p)
/*@ With x l
    Require p != 0 && sll(p, cons(x, l))
    Ensure __return == x && sll(p@pre, cons(x, l))
*/
{
    return p->data;
}
