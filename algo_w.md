# Typed JQ Inference



# Typing Rules
Variable lookup:
 $$ \frac {x: \sigma \in \Gamma \quad \tau=\text{inst}(\sigma) } {\Gamma \vdash x : \tau}  $$

Variable bindings:
 $$\frac {\Gamma, x: \alpha \vdash e : \tau \quad \alpha \text{ fresh}} {\Gamma \vdash \lambda x . e : \alpha \rightarrow \tau}$$