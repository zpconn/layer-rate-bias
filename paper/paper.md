# Steering a network’s inductive bias with the hidden-layer learning rate

**Author** Zach Conn

**Abstract.** Can the initial predictions of a network tell us which of two learning rates will yield the larger population mean after training? For two-layer ReLU networks trained on an odd grid of $N$ points on the circle, the initial grid deficit $X$ predicts both the ordering and its size. Starting both copies from the same Gaussian seed and changing the hidden-layer rate from $1/2$ to $2$ gives a slow-minus-fast gap of $(\pi^2/40)X/N^2+o_p(N^{-2})$ at a common deterministic endpoint. The kernel calculation gives an exact positive coefficient $c_N$ for every odd $N\ge3$. For a smaller GD step we prove a finite-grid guarantee at widths proportional to $N^{16}$. The nonlinear unit-step and flow guarantees at this endpoint use width $N^{32}$ and very large sufficient grid sizes. Flow tracks its reference in mean square, while rare seeds make the corresponding fixed-step mean-square prediction error diverge. The slope shortfall decreases with width on all five grids. Over 512–524,288 neurons, single power-law fits give exponents of 0.40–0.47, decreasing with grid size. At intermediate widths the local exponents are close to one half. We formalize the training theorems in Lean 4 with Mathlib and separately check arithmetic on the frozen numerical records.

## Introduction {.unnumbered}

How much does fitting the labels tell us about the network between training points? For the circle grid studied here the answer can be made exact. At every odd $N\ge3$ and width $m\ge N+5$, for **each** real $s$ there are network parameters that interpolate the labels exactly and have population mean $s$. There is also a probabilistic statement for equal-rate GD with Gaussian initialization. For any finite search cap and positive fit tolerance, conditional on hitting the tolerance, the population mean at the first hit has support on the entire real line. Thus fit alone leaves the mean undetermined. The paired experiment asks what can be predicted when the rates change and the seed is held fixed. [Exact interpolation](../formal/CircleFitSupport.lean#L63) · [First-hit support](../formal/CircleFitSupport.lean#L244)

Practitioners choose different learning rates for different parts of a model. ULMFiT fine-tunes earlier and later layers at different rates, LARS adapts updates to layer norms, and LoRA+ assigns different rates to the two factors of a low-rank update [@howard2018; @you2017; @hayou2024]. Two-timescale theory also studies how relative layer speeds affect convergence [@marion2023]. Here one multiplier changes in an otherwise identical pair. We measure its effect on the fitted function away from the data.

We use **inductive bias** to mean the choice of extension away from the grid. Once the grid is fit, the discrepancy between the circular average and the target average comes from the behavior between sample points. **Statistical bias** is the signed error of the expected prediction, averaged over initialization. A pair can have a predictable ordering for a given seed even when neither copy has a small absolute error for that seed.

- For every odd grid, the two kernel interpolants transfer different, exactly calculable fractions of the initial grid deficit into their circular means. The slower hidden layer transfers more.
- At every odd $N\ge3$, explicit GD step and width choices yield an error bound that holds at every sufficiently late common step. At the common horizon for unit-step GD and flow, the initial deficit predicts the sign and leading magnitude of this gap for the trained networks with high probability. The flow statement covers every measurable selection of Clarke solutions.
- Gradient flow also tracks in $L^2$. Unit-step descent exhibits a different tail behavior even though its typical seeds obey the prediction. We give machine-checked proofs and compare the finite-grid formula with paired numerical runs.

![At $N=3$, the constant and $\cos(2Nu)$ agree at all three nodes. The cosine averages to zero around the circle. For a unit residual at every node, both kernel corrections fit the grid. Their circular means differ because the two kernels assign different weights to the aliases.](kernel-alias.png)

**Regime.** The finite-grid GD guarantee (Theorem 1) applies at every odd $N\ge3$, with a step at most $2/3$ for the benchmark pair. Its sufficient width is $1.44\times10^{18}N^{16}$, still about $6.2\times10^{25}$ neurons at $N=3$. The kernel slope is exact for every odd $N\ge3$. At the common horizon $H$, the sufficient grid cutoff for simultaneous fitting and tracking with unit-step GD is $4^{32}$, so the first admissible odd grid has $4^{32}+1$ points and width greater than $2^{2048}\simeq3.23\times10^{616}$. The paired flow event starts at $N=36{,}865$, giving $m\simeq1.35\times10^{146}$. By comparison, $3^{32}\simeq1.85\times10^{15}$, while the primary three-point experiments in Section 4 used widths up to $32{,}768$. The GD cutoff arises when the proof bounds the terminal residual by $4N^{-97/32}$ and requires this to be at most $N^{-3}$. [GD horizon](../formal/CirclePairedGDClock.lean#L52) · [GD event](../formal/CirclePairedGDTypical.lean#L208) · [Flow event](../formal/CirclePairedTheorem.lean#L41)

## Related work {.unnumbered}

**Tangent kernels and lazy training.** Gradient descent induces a kernel on network outputs. In the infinite-width tangent regime the kernel freezes, and training follows the linearization at initialization [@jacot2018; @lee2019]. Scaling can itself produce this linear behavior [@chizat2019]. For wide two-layer networks there are quantitative results on convergence to zero training loss and on generalization through a related kernel [@du2019; @arora2019]. Our question begins where a training-loss guarantee ends: what does the fitted network predict between observations?

**Parametrization and layer scale.** In shallow univariate ReLU regression, relative initialization scales can change the learning regime and the resulting interpolant [@williams2019]. An initialization-dependent curvature penalty characterizes wide two-layer fits in further settings [@jin2023]. Standard parametrization and the broader classification of infinite-width limits make explicit which layer scales survive in the training dynamics [@sohl2020; @yang2021]. Here both copies stay in the kernel regime. The rate ratio changes the relative contribution of the two parameter blocks to the tangent kernel, and we compute its effect on a particular observable of the trained pair.

**Spectral bias away from the data.** Arc-cosine kernels describe angular dependence from rectified Gaussian features [@cho2011]. Spectral analyses relate activation, geometry and frequency to approximation and learning speed [@bietti2019; @basri2019; @rahaman2019]. Bowman and Montúfar bound how closely finite networks follow population kernel dynamics away from their training sets [@bowman2022]. In our finite grid, harmonics separated by multiples of the grid size are indistinguishable at every observed node. Their relative kernel weights determine how much of a constant grid residual contributes to the population mean. Related symmetry reductions in kernel quadrature give a single weight per orbit of a fully symmetric design [@karvonen2018].

**Initial output.** Kernel regression from a random initial function retains a component of that function away from the data. Zhang et al. quantify its contribution to regression error and give an antisymmetric initialization with zero initial output [@zhang2020]. Sharing the initialization lets us use its observable grid deficit as a predictor of the difference between two fitted networks.

**Nonsmooth flows.** A ReLU gate can change sign on the training set. Differential inclusions and generalized gradients give precise notions of a solution at such points [@clarke1990; @filippov1988; @aubin1984]. Conservative fields give a calculus for derivatives returned by automatic differentiation in nonsmooth models [@bolte2021]. Our flow results quantify over measurable choices of admissible trajectories. The existence and selection proofs are part of the formal development. The weighted squared-norm difference monitored in the simulations is related to the balance invariants of homogeneous gradient flow [@du2018].

**Euler schemes and rare events.** Explicit Euler can have divergent moments for superlinear stochastic differential equations [@hutzenthaler2011]. Theorem 2.1 of @hutzenthaler2013 also permits zero diffusion when the initial law satisfies its lower tail bound. Their §4 uses the scalar drift $-x^5$ with Gaussian initial data. A tamed Euler method restores strong convergence under the assumptions of @hutzenthaler2012. Separately, @gyongy1998 proves almost-sure convergence for Euler approximations under a drift monotonicity condition and Lipschitz diffusion. These examples motivate distinguishing trajectory or distributional statements from bounds on moments. Our unstable iterates arise from the gradient update of a finite network.

**Finite-width corrections.** The tangent kernel fluctuates at initialization [@hanin2020] and can evolve during training. Diagram expansions and the neural tangent hierarchy describe corrections to infinite-width dynamics [@dyer2020; @huang2020]. Effective-theory expansions also relate deviations from Gaussian predictions to the network's aspect ratio [@roberts2022]. The width dependence measured here concerns a particular regression slope across shared seeds. Its coefficient is estimated from the paired experiments.

**Initialization variance and ensembles.** Random-feature models separate initialization variance from sampling and label variance, and quantify what averaging independent fits removes [@adlam2020; @dascoli2020]. Geiger et al. measure how fluctuations from initialization change with width and ensembling [@geiger2020]. With training data and initialization shared, one can instead ask which of two choices of layer rate will give the larger mean on the same seed.

**Formal verification.** Lean 4 checks formal derivations [@demoura2021]. Mathlib supplies definitions and lemmas for classical mathematics [@mathlib2020]. The statement audit relates the definitions used by the checker to the network, sampling law and observables appearing here.

## Model and training dynamics

> **Definition 1.1 (Network and means).** Fix an odd $N\ge3$, a positive width $m$, and $u_i=2\pi i/N$ for $0\le i<N$. At angle $u$ the input is $x(u)=(\cos u,\sin u)$ and the label is $y(u)=1+\cos u$. Write $Q_N$ for the arithmetic mean on the grid and $Q$ for the uniform angular mean. For readouts $a_j\in\mathbb{R}$ and hidden weights $w_j\in\mathbb{R}^2$, set
>
> $$
> f_\theta(u)=\frac1{\sqrt m}\sum_{j=1}^m a_j[w_j^\top x(u)]_+,
> \qquad [z]_+=\max(z,0).
> $$
>
> The seed $\theta_0$ consists of $3m$ independent standard Gaussian coordinates. Both copies start at this seed and have the same initial predictor $f_0$. The **initial grid deficit** is $X=1-Q_Nf_0$.

The labels have mean $Q_Ny=Qy=1$. For any trained or untrained network the population mean has the exact form $Qf_\theta=(\pi\sqrt m)^{-1}\sum_j a_j\|w_j\|$. Indeed, rotating a neuron’s hidden direction to the horizontal axis gives the feature $\|w_j\|[\cos u]_+$, whose integral over a full turn is $2\|w_j\|$. Almost every angle contributing to $Q$ lies outside the training set. [Network](../formal/CircleFlowPath.lean#L60) · [Seed law](../formal/CircleEscapeBridge.lean#L73) · [Angular integral](../formal/CircleAngularGeometry.lean#L54)

> **Definition 1.2 (Paired training rules).** Let $r_i=f_\theta(u_i)-y(u_i)$, $\|r\|_N^2=N^{-1}\sum_i r_i^2$, and $L=\|r\|_N^2/2$. The readout multiplier is one, and the hidden multiplier $\tau$ is $1/2$ in the slow copy and $2$ in the fast copy. With base step $\eta$, simultaneous full-batch gradient descent (GD) uses
>
> $$
> \begin{aligned}
> a_j^+ &= a_j-\frac{\eta}{\sqrt m}Q_N\!\left(r[w_j^\top x]_+\right),\\
> w_j^+ &= w_j-\frac{\eta\tau}{\sqrt m}\,a_j Q_N\!\left(r\,\mathbf 1_{\{w_j^\top x>0\}}x\right).
> \end{aligned}
> $$
>
> All quantities on the right use the old weights, and the ReLU slope at zero is zero. For gradient flow let $D_\tau$ multiply readout coordinates by one and hidden coordinates by $\tau$. A flow is an absolutely continuous solution of $\dot\theta\in-D_\tau\partial_C L(\theta)$ almost everywhere, with $\partial_C L$ the Clarke subdifferential.

Global flows admit a Borel selection as a function of the seed. All flow conclusions hold for every measurable selection of a solution for each copy. [Simultaneous update](../formal/CircleWeightedStep.lean#L23) · [Global Clarke flow](../formal/CircleFlowConstruction.lean#L75)

For $\tau>0$, write $w_j=\sqrt\tau\,v_j$ and initialize $v_j$ with covariance $I/\tau$. Positive homogeneity gives $f=(\sqrt\tau/\sqrt m)\sum_j a_j[v_j^\top x]_+$. In these coordinates the chain rule gives $\partial_{v_j}L=\sqrt\tau\,\partial_{w_j}L$. Plain descent on $(a,v)$ therefore sends $a_j$ to $a_j-\eta\partial_{a_j}L$ and $w_j$ to $w_j-\eta\tau\partial_{w_j}L$. The same linear change of variables carries admissible flow paths in both directions, including at gate crossings. This reparametrization preserves the initial function when the underlying $w_j$ draw is shared. It explains why the hidden-gradient term in the tangent kernel is weighted by $\tau$ [@williams2019; @yang2021]. [Scaled output](../formal/CircleReparametrization.lean#L27) · [GD step](../formal/CircleReparametrization.lean#L54) · [Flow correspondence](../formal/CircleReparametrization.lean#L91) · [Transformed seed law](../formal/CircleReparametrization.lean#L114)

For the paired comparison, fix the width $m=N^{32}$ and the deterministic horizon

$$
H=\left\lceil2\pi^2 N^2\log\!\left(2\sqrt{12}\,N^{7/2}\right)\right\rceil .
$$

Within a pair, take $H$ GD updates with $\eta=1$, or evolve both flows to time $H$. Write $Y_\tau=Qf_{\tau,H}$ and $\Delta=Y_{1/2}-Y_2$. A run **fits** if $\|r_H\|_N\le N^{-3}$. A **wrong ordering** is the event $\Delta X\le0$, with a tie counted as a miss. All probabilities and $L^p$ norms of random variables use the Gaussian seed law. [Training horizon](../formal/CircleFlowTracking.lean#L347) · [Ordering event](../formal/CirclePairedOrdering.lean#L42)

| Notation | Meaning |
| --- | --- |
| $N,m,H$ | Grid size, hidden width and common training horizon |
| $Q_N,Q$ | Uniform averages on the grid and around the circle |
| $X$ | Initial grid deficit, $Q_N(y-f_0)$ |
| $b_{\tau,N},Z_\tau$ | Kernel quadrature weight summed over the grid, and reference population mean |
| $Y_\tau,\Delta$ | Trained population mean and the slow-minus-fast gap |
| $c_N$ | Exact slope of the scaled reference gap against $X$ |

## The finite-grid coefficient

Let $K_\tau$ denote the grid operator of the initialization-averaged tangent kernel,
$(K_\tau r)_i=N^{-1}\sum_j k_\tau(u_i,u_j)r_j$. The factor $1/N$ comes from the training loss. For $h(s)=[\cos s]_+$, write $h_k=(2\pi)^{-1}\int_{-\pi}^{\pi} h(s)e^{-iks}\,ds$.

> **Lemma 2.1 (Spectrum of the sampled tangent kernel).** Fix an odd $N\ge3$ and $0<\tau\le2$. The Fourier coefficient of $k_\tau(\cdot,0)$ at integer $k$ is $a_{\tau,k}=[2+\tau(1+k^2)]|h_k|^2$. On the grid character $j\mapsto e^{i\ell u_j}$, the eigenvalue of $K_\tau$ is
>
> $$
> \lambda_{\tau,\ell}=\sum_{k\equiv\ell\pmod N}a_{\tau,k},
> \qquad
> \frac{\tau}{(\pi N)^2}\le\lambda_{\tau,\ell}\le\frac{1+\tau}{2}.
> $$
>
> In particular, with $g_\tau=\tau/(\pi N)^2$, every grid residual vector $r$ satisfies $\|(I-K_\tau)r\|_N\le(1-g_\tau)\|r\|_N$.

**Proof idea.** Averaging a feature over random rotations diagonalizes its covariance in Fourier coordinates. The hidden gradient differentiates the angular feature, giving extra weight to high frequencies. The grid identifies frequencies in the same residue class modulo $N$. When $N$ is odd, every class contains an even mode on which the hidden derivative supplies a positive spectral lower bound.

**Proof.** Write a Gaussian hidden weight as $R(\cos\phi,\sin\phi)$. Its angle is uniform and independent of $R$, with $\mathbb{E}[R^2]=2$. Before the network normalization, the readout derivative at angle $u$ is $Rh(u-\phi)$. The sum over the $m$ neurons cancels the $1/m$ from the two gradients. If $d\in[0,\pi]$ is the angular distance between two inputs, both readout features are active on an arc of length $\pi-d$. The integral of $\cos s\cos(s-d)$ over this arc is $[\sin d+(\pi-d)\cos d]/2$. The hidden derivative contributes the input dot product $\cos d$ on the same arc, weighted by $\tau$ and by the independent readout's second moment, one. Thus

$$
k_\tau(u,v)=\frac{\sin d+(1+\tau)(\pi-d)\cos d}{2\pi}.
$$

Evenness gives $h_k=\pi^{-1}\int_0^{\pi/2}\cos s\cos(ks)\,ds$. The product-to-sum identity yields $h_{2j}=(-1)^j/[\pi(1-4j^2)]$ and $h_k=0$ at odd $|k|\ge3$. At $k=\pm1$ the integral of $\cos^2 s$ gives $h_k=1/4$. The covariance of a translated feature has Fourier coefficients equal to the squared moduli of the feature coefficients. In the radial and tangential unit directions of the hidden weight the derivatives are $h$ and $-h'$ times the readout. A tangential displacement of length one changes the angle at rate $1/R$, which cancels the $R$ in the feature. Integration by parts on its smooth arcs gives the derivative coefficient $ik h_k$ because $h$ is continuous and periodic. The readout and the two hidden derivatives therefore contribute $2|h_k|^2$, $\tau|h_k|^2$ and $\tau k^2|h_k|^2$, respectively. In particular $a_{\tau,0}=(2+\tau)/\pi^2$ and the coefficients are absolutely summable, decaying as $O(k^{-2})$.

Insert this series into $K_\tau$ applied to the grid character of frequency $\ell$. The grid average of $e^{i(\ell-k)u_j}$ is one for $k\equiv\ell\pmod N$ and zero otherwise. This proves the alias sum. The constant-mode eigenvalue is at least $a_{\tau,0}\ge g_\tau$. In each nonzero residue, oddness of $N$ gives even representatives $j$ and $j-2N$ with $0<j<2N$. At nonzero even $k$ the explicit coefficient gives $a_{\tau,k}\ge\tau/(\pi^2 k^2)$. By convexity of $x\mapsto x^{-2}$ at $j$ and $2N-j$, these two representatives already contribute $2g_\tau$ or more. For the upper bound, $|\sin d|\le d$ and $|\cos d|\le1$ in the angular formula give $|k_\tau(u,v)|\le(1+\tau)/2$, which bounds the absolute row sums of the normalized matrix. Since $g_\tau\le1/2$ and $(1+\tau)/2\le3/2$, its real eigenvalues satisfy $|1-\lambda_{\tau,\ell}|\le1-g_\tau$. The characters form an orthogonal basis for the grid inner product, giving the residual bound.

$\square$

**Lean proof.** The formalization integrates the angular kernel to identify the same Fourier coefficients. The spectral gap and the upper operator bound give contraction at unit step. [`angular_tangent`](../formal/CircleKernelIdentification.lean#L115) · [`cartesian_kernel_isotropic`](../formal/CircleKernelIdentification.lean#L539) · [`halfWaveCoeff_formula`](../formal/CircleSpectrum.lean#L29) · [`tangentFourier_piecewise`](../formal/CircleKernelIdentification.lean#L329) · [`summable`](../formal/CirclePositiveSpectrum.lean#L20) · [`sampled_character_eigenvalue`](../formal/CircleGridSpectrum.lean#L241) · [`alias_gap`](../formal/CirclePositiveSpectrum.lean#L28) · [`operator_upper`](../formal/CirclePositiveSpectrum.lean#L157) · [`unit_contraction`](../formal/CirclePositiveSpectrum.lean#L212)

For an actual network update with $\|r_{t+1}-(I-K_\tau)r_t\|_N\le e_t\|r_t\|_N$, the triangle inequality now gives $\|r_{t+1}\|_N\le(1-g_\tau+e_t)\|r_t\|_N$. This is the estimate used in the nonlinear argument. [`grid_defect`](../formal/CircleWeightedStep.lean#L147) · [`trajectory_of_contraction`](../formal/CircleWeightedDynamics.lean#L181)

For the constant grid mode, write $k_j=2Nj$ for $j\ge1$ and introduce the positive alias sums

$$
A=2\sum_{j\ge1}\frac{1}{(k_j^2-1)^2},
\qquad
B=2\sum_{j\ge1}\frac{k_j^2}{(k_j^2-1)^2}.
$$

Write $Z_\tau$ for the population mean of the fixed-kernel interpolant obtained by starting at $f_0$ and fitting the grid.

> **Proposition 2.2 (Exact finite-grid prediction).** For every odd $N\ge3$ and every continuous target $y$ and continuous initial predictor $f_0$, the two fixed-kernel interpolants satisfy $N^2(Z_{1/2}-Z_2)=c_N X$, where $X=Q_N(y-f_0)$ and
>
> $$
> c_N=\frac{(3/10)N^2B}{(1+A+B/5)(1+A+B/2)}>0.
> $$
>
> In particular, the reference contrast has the sign of $X$, including equality at $X=0$.

**Proof idea.** A kernel update changes the population and grid means in a fixed ratio. To find that ratio, compare the constant coefficient on the whole circle with the sum of all the frequencies that look constant on the grid.

**Proof.** A kernel column has population mean $a_{\tau,0}$ and grid mean $\lambda_{\tau,0}$. For the unit-step kernel iteration $f_t^{\mathrm{ker}}$ started at $f_0$, write $r_t$ for the grid residual. One update changes the population mean by $-a_{\tau,0}Q_Nr_t$ and the grid mean by $-\lambda_{\tau,0}Q_Nr_t$. Hence $Q f_t^{\mathrm{ker}}-b_{\tau,N}Q_N f_t^{\mathrm{ker}}$ is invariant, where $b_{\tau,N}=a_{\tau,0}/\lambda_{\tau,0}$. By Lemma 2.1, $\|r_t\|_N\le(1-g_\tau)^t\|r_0\|_N$, so $Q_N f_t^{\mathrm{ker}}\to Q_Ny$. The limiting population mean is $Z_\tau=Qf_0+b_{\tau,N}X$. At each finite step the same invariant gives $Q f_t^{\mathrm{ker}}-Z_\tau=b_{\tau,N}Q_N r_t$. Thus every residual component with zero grid average makes zero contribution to this population-mean error.

An odd multiple of $N$ has magnitude at least three and zero Fourier coefficient. The only nonzero aliases of the constant mode with nonvanishing weight are therefore $\pm k_j$. For these frequencies $|h_{k_j}|^2=1/[\pi^2(k_j^2-1)^2]$. Dividing the alias sum in Lemma 2.1 by $a_{\tau,0}=(2+\tau)/\pi^2$ gives

$$
b_{\tau,N}^{-1}=1+A+\frac{\tau}{2+\tau}B .
$$

The multiplier of $B$ is $1/5$ at rate $1/2$ and $1/2$ at rate $2$. Taking reciprocals, subtracting the weight at rate $2$ from the weight at $1/2$, and multiplying by $N^2$ gives the stated $c_N$. The common initial term $Qf_0$ cancels in the difference $Z_{1/2}-Z_2$. Every summand of $B$ is positive, fixing the sign for each initialization.

$\square$

**Lean proof.** The constant-mode and population row identities identify the interpolation weight. The exact difference and its strict sign hold for any common initial population and grid means. [`constant_alias_eq`](../formal/CircleGridSpectrum.lean#L356) · [`cartesian_integrated_row`](../formal/CircleGridSpectrum.lean#L524) · [`population_row_factorization`](../formal/CircleGridSpectrum.lean#L550) · [`weight_exact`](../formal/CircleFiniteCoefficient.lean#L88) · [`weight_difference`](../formal/CircleFiniteCoefficient.lean#L100) · [`paired_reference_exact`](../formal/CircleFiniteCoefficient.lean#L118) · [`paired_reference_slow_wins_iff`](../formal/CircleFiniteCoefficient.lean#L125)

For an arbitrary vector of label residuals, $Z_\tau-Qf_0=b_{\tau,N}Q_N(y-f_0)$ is a kernel quadrature rule. Rotation by one grid spacing permutes its nodes while leaving the kernel and integration measure invariant, so each node gets the same weight $b_{\tau,N}/N$ [@karvonen2018]. For each nonzero even alias $k$ of the constant, its weight relative to that constant is $[2+\tau(1+k^2)]/[(2+\tau)(k^2-1)^2]$. Increasing $\tau$ increases this ratio and reduces the fraction of the residual transferred to the population mean.

> **Corollary 2.3 (Second-order coefficient).** On every odd grid with $N\ge3$,
>
> $$
> \left|c_N-\left(\frac{\pi^2}{40}-\frac{\pi^4}{1600N^2}\right)\right|
> \le \frac{400}{N^4}.
> $$

**Proof idea.** The first two terms in $B$ come from the inverse squares and inverse fourth powers of the even aliases. To second order, one must also account for the appearance of $B$ in the denominator of Proposition 2.2.

**Proof.** Put $t=N^{-2}$ and $z_j=(2Nj)^{-2}=t/(4j^2)$. The summands of $A$ and $B$ are $2z_j^2/(1-z_j)^2$ and $2z_j/(1-z_j)^2$. For $0\le z\le1/4$,

$$
0\le\frac{2z}{(1-z)^2}-(2z+4z^2)
=\frac{2z^3(3-2z)}{(1-z)^2}\le12z^3 .
$$

Using $\sum_{j\ge1}j^{-2}=\pi^2/6$ and $\sum_{j\ge1}j^{-4}=\pi^4/90$, the sum of $2z_j+4z_j^2$ is $bt+dt^2$, where $b=\pi^2/12$ and $d=\pi^4/360$. Since $2z_j^2/(1-z_j)^2\le t^2/j^2$ and $12z_j^3\le t^3/j^2$, summing the bounds gives $0\le A\le3t^2$ and $0\le B-bt-dt^2\le3t^3$. Write $W=B/t=b+dt+et^2$, with $0\le e\le3$.

Let $D=(1+A+B/5)(1+A+B/2)$ denote the exact denominator. Its expansion is $D=1+pt+qt^2$, where $p=7b/10$ and

$$
q=2A/t^2+(7/10)(d+et)+(A/t+W/5)(A/t+W/2).
$$

Here $0<t\le1$, $0\le b\le2$, $0\le d\le1$, and $0\le W\le6$, so $0\le q\le40$ and $D\ge1$. Put $g=d-bp$. The linear terms cancel in the exact identity

$$
W-(b+gt)D=t^2\bigl[e-gp-(b+gt)q\bigr].
$$

The absolute value of the bracket is at most $3+4\cdot2+6\cdot40$, since $|g|\le4$ and $|b+gt|\le6$. Proposition 2.2 gives $c_N=(3/10)W/D$. Dividing the identity by $D$ and multiplying by $3/10$ bounds the error by $400t^2$. Finally $(3/10)b=\pi^2/40$ and $(3/10)g=-\pi^4/1600$, giving the claimed expansion.

$\square$

**Lean proof.** The alias estimates control the remainders before division by the positive denominator. [`coefficient_second_order`](../formal/CircleFiniteCoefficient.lean#L231) · [`aliases`](../formal/CircleCoefficientRemainder.lean#L56) · [`uniform_remainder`](../formal/CircleCoefficientRemainder.lean#L91)

Set $\theta=\pi/(2N)$. The alias sums $A_N=A$ and $B_N=B$ in the exact coefficient can be evaluated without truncating a Fourier series,
$$
 A_N=-1+\tfrac12\theta\cot\theta+\tfrac12\theta^2\csc^2\theta,
 \qquad B_N=\tfrac12\theta^2\csc^2\theta-\tfrac12\theta\cot\theta.
$$
Substituting in $b_{r,N}=[1+A_N+r B_N/(2+r)]^{-1}$ gives the following values of $c_N(1/2,2)$, rounded to ten places. [Alias sums](../formal/CircleClosedForms.lean#L125) · [Constant mode](../formal/CircleClosedForms.lean#L162) · [Exact weight](../formal/CircleFiniteCoefficient.lean#L88)

The closed form also gives the higher-order expansion
$$
 c_N=\frac{\pi^2}{40}-\frac{\pi^4}{1600N^2}
       -\frac{31\pi^6}{448000N^4}
       +\frac{13\pi^8}{69120000N^6}+O(N^{-8}).
$$
The absolute fourth-order coefficient is about $0.0665$. Corollary 2.3 bounds the entire remainder by $400/N^4$ uniformly, which at $N=3$ exceeds the coefficient itself. For that grid the exact formula gives $0.2391588734$. [Higher-order expansion](../formal/CircleCoefficientExpansion.lean#L111)

**Table 1.** Finite-grid coefficients from the closed form, with their large-grid limit.

| $N$ | $c_N$ | $N$ | $c_N$ | $N$ | $c_N$ |
|---:|---:|---:|---:|---:|---:|
| 3 | 0.2391588734 | 9 | 0.2459783609 | 21 | 0.2466017166 |
| 5 | 0.2441985927 | 11 | 0.2462324212 | 31 | 0.2466766866 |
| 7 | 0.2454699576 | 15 | 0.2464682153 | $\infty$ | 0.2467401100 |

> **Proposition 2.4 (Fourier coefficients of the kernel interpolant).** For an arbitrary continuous target $y$, set $r_j=y(u_j)-f_0(u_j)$ and $\widehat r_\ell=N^{-1}\sum_j r_j e^{-i\ell u_j}$. On an odd grid $N\ge3$ and for $1/2\le\tau\le2$, the correction from tangent-kernel interpolation has, at every integer frequency $k$, coefficient
> $$
>  \widehat{(f_{\rm ref}-f_0)}(k)
>    =\frac{a_{\tau,k}}{\lambda_{\tau,\ell}}\widehat r_\ell,
>  \qquad \ell=k\bmod N,\quad \lambda_{\tau,\ell}=\sum_{h\equiv\ell\bmod N}a_{\tau,h}.
> $$

**Proof.** The grid convolution is diagonal in the discrete Fourier basis, and a kernel section centered at $u_j$ has coefficient $e^{-iku_j}a_{\tau,k}$. Solving the grid equations supplies the reciprocal eigenvalue. At $k=0$ this is the equal-weight quadrature formula $Qf_{\rm ref}=Qf_0+b_{\tau,N}Q_N(y-f_0)$. Thus two rate choices differ by $(b_{\tau,N}-b_{\sigma,N})Q_N(y-f_0)$ even when $Q_Ny\ne Qy$. To compare a single copy to the true target mean, write $Qf_{\rm ref}-Qy=(Qf_0-Q_Nf_0)+(b_{\tau,N}-1)Q_N(y-f_0)+(Q_Ny-Qy)$. The last term is the target's quadrature error. [All Fourier modes](../formal/CircleFourierInterpolant.lean#L39) · [Mean for a general target](../formal/CircleFourierInterpolant.lean#L92)

$\square$

For $1+\cos u$, the three target modes $0,1,-1$ occupy distinct residues on every odd grid $N\ge3$. The target has $Q_Ny=Qy=1$, $|y|\le2$ and $Q_N y^2=3/2$. The nonlinear training bounds use the specified labels in controlling the initial residual and its Fourier components. The kernel formula for a general target does not establish those estimates for other labels. At equal rates the development also identifies the first cosine amplitude $2Q(f\cos u)$ of an actual network with $(2\sqrt m)^{-1}\sum_j a_j w_{j,1}$, constructs its kernel interpolant and computes the first two moments of its reference amplitude. Nonlinear tracking of the entire interpolant remains open. [Cosine amplitude](../formal/CircleFirstCosine.lean#L51) · [Interpolating solution](../formal/CircleFirstCosineReference.lean#L444) · [Reference moments](../formal/CircleFirstCosineReference.lean#L263)

## Main results

We now compare the actual training trajectories with the kernel reference. Their initial deficit is the same, so subtracting the two reference means gives the exact scaled gap $c_NX$. All limits below are along odd $N\to\infty$. [Finite-grid coefficient](#the-finite-grid-coefficient)

> **Theorem 1 (Common endpoint for finite-grid GD).** For a hidden multiplier $r>0$, write $M_r(N)=(\lceil 3\cdot10^8(\max(1,r)/r)^2\rceil N^8)^2$. Choose $0<\tau<\sigma$ and a base step $0<\eta\le2/(1+\sigma)$. At every odd $N\ge3$ and every common width $m\ge\max(M_\tau,M_\sigma)$, there is a measurable event of probability at least $1-2/N$ on which both copies fit to RMS $N^{-3}$ and
> $$
> \left|N^2(Y_\tau(t)-Y_\sigma(t))-c_N(\tau,\sigma)X\right|\le 2/N,
> \qquad c_N(\tau,\sigma)=N^2(b_{\tau,N}-b_{\sigma,N}).
> $$
> Here $Y_r(t)$ denotes the population mean after update $t$. These bounds hold simultaneously at every integer step from the larger of the two individual deadlines onward. The deadline for $r$ is at most $\lceil192 N^2\log N/(\eta r)\rceil$. In particular the rates $1/2$ and $2$ admit the common width $1.44\cdot10^{18}N^{16}$ and every step $0<\eta\le2/3$. This gives a finite-grid result for a smaller base step than the unit-step benchmark. Its error bound at small $N$ can exceed the signal. [Single-rate deadline](../formal/CirclePositiveSchedule.lean#L121) · [Persistence past the deadline](../formal/CirclePositiveWidth.lean#L71) · [Common-seed GD](../formal/CircleRateDial.lean#L53)

**Proof.** Each single-rate theorem also gives convergence of the parameters to an exact grid interpolant on its good event. The one-rate bound gives geometric decay of the training residual and a uniform bound on the total residual accumulated through each step. The former decreases after the deadline and the latter controls the error in the signed population-minus-grid update. Taking the intersection of the two single-rate events costs at most $2/N$ in probability under the shared seed law.

$\square$

> **Theorem 2 (discrete GD).** For all sufficiently large odd $N$, there exists an event of probability at least $1-2/\sqrt N$ on which both copies fit and
>
> $$
> \left|N^2\Delta-c_N X\right|\le10N^{-33/32}.
> $$
>
> The probability of a wrong ordering is $O(N^{-1/2})$, and $N^2\Delta-(\pi^2/40)X\to0$ in probability. For every bounded deterministic sequence $d_N$, including $c_N$ and $\pi^2/40$, the unscaled mean-square error satisfies
>
> $$
> \mathbb{E}\!\left[\left(\Delta-\frac{d_N X}{N^2}\right)^2\right]\longrightarrow+\infty .
> $$

**Proof idea.** On typical seeds each trajectory tracks its kernel reference. The references differ by exactly $c_N X/N^2$. A second argument finds rare common seeds for which the fast network’s output outgrows the slow network’s by enough to dominate the second moment.

**Proof.** Lemma 5.1 gives one event per rate. Intersecting them costs at most $2/\sqrt N$ in probability. Each copy fits there and each endpoint differs from its reference by at most $5N^{-97/32}$. Subtracting the two endpoints and multiplying by $N^2$ gives $10N^{-33/32}$. Proposition 5.2 applies the Gaussian bound for $\Pr(|X|\le N^{-1/2})$ to obtain the ordering estimate, and uses $\sup_N\mathbb{E}X^2\le3/2$ and $c_N\to\pi^2/40$ to pass to the limiting slope in probability. For the second moment, $H/\log N\to\infty$, so $H\ge60\log N$ eventually. Proposition 6.2 at $T=H$ gives the stated divergence for every bounded $d_N$. Each expectation is finite at finite $N$. [Lemma 5.1](#a-bound-for-the-entire-trajectory) · [Proposition 5.2](#the-paired-endpoint) · [Proposition 6.2](#gaussian-mass-and-squared-prediction-error)

$\square$

**Lean proof.** [Paired discrete gradient descent](../formal/CirclePairedGDTheorem.lean#L59) · [All bounded coefficient sequences](../formal/CirclePairedGDClocksTail.lean#L49) · [Finite endpoint moments](../formal/CirclePairedGDIntegrable.lean#L156)

The asymptotic behavior of the signed mean $\mathbb{E}[\Delta]$ for unit-step GD remains open.

**Step size, moments and distribution.** The fixed-step divergence proof exhibits a particular set of seeds on which the squared separation grows faster than the reciprocal of its probability. For fixed $\eta>0$, this witness box has probability $\exp[-\Theta_\eta(m(T+\log N+1))]$. Indeed, its $3m$ coordinates occupy intervals of length $\ell=(8N\,512^{2T})^{-1}$. The standard Gaussian density on those intervals lies between $e^{-(R_{\eta}+1)^2/2}/\sqrt{2\pi}$ and $1/\sqrt{2\pi}$, for the box-center magnitude $R_{\eta}$ of Lemma 6.1. Multiplying the coordinate bounds gives the stated scale. This quantifies one contribution to the second moment. [Lower box probability](../formal/CircleSynchronizedWidth.lean#L59) · [Upper box probability](../formal/CircleSynchronizedWidth.lean#L324)

At **equal layer rates**, a single curvature measurement at initialization separates the distributional and moment conclusions. Let $\Lambda_0$ be the largest eigenvalue of $J_0J_0^\top/N$ and use the constant step $1/\max(1,\Lambda_0)$. At $m=N^{32}$ and $H$, the resulting unconditional RMS reference error is $O(N^{-15})$ for odd $N\ge12{,}000{,}001$. This cap agrees with a unit step except on a set of probability at most $e^{-m/240}$ for odd $N\ge81$. Consequently the capped and unit-step learners have the same limit in distribution, even at $H$, where the unit-step second moment diverges. For every schedule $\lceil\pi^2\log N\rceil\le T\le385N^3$, their scaled outputs $N^2(Y_T-1)$ both converge in law to $\mathcal N(-\pi^2/36,7\pi^2/1620)$ as odd $N\to\infty$. The initialization cap illustrates the role of taming an explicit Euler step in moment estimates [@hutzenthaler2012]. [Capped RMS](../formal/CircleSharpGDMoments.lean#L248) · [Rejection probability](../formal/CircleCapMoments.lean#L295) · [Capped limit](../formal/CircleGaussianLimit.lean#L158) · [Fixed-step limit](../formal/CircleGaussianLimit.lean#L181)

> **Theorem 3 (gradient flow).** For all sufficiently large odd $N$, there exists an event of probability at least $1-96N^{-158}$ on which both copies fit and $|N^2\Delta-c_NX|=O(N^{-13}\log N)$. The probability of a wrong ordering is $O(N^{-13})$. Over all seeds,
>
> $$
> \left\|\Delta-\frac{c_N X}{N^2}\right\|_{L^2}=O(N^{-15}),
> \qquad
> \mathbb{E}[\Delta]=\frac{\pi^2}{40N^2}+O(N^{-4}).
> $$

**Proof idea.** Loss dissipation controls even exceptional trajectories, so the two tracking errors can be subtracted in $L^2$. For the sign, conditioning on a random direction in readout space bounds the probability that the initial deficit is small compared with the error for that same seed.

**Proof.** Proposition 7.2 supplies the common fitting and tracking event. For each rate let $e_\tau=Y_\tau-Z_\tau$. Since $\Delta-c_NX/N^2=e_{1/2}-e_2$ exactly, its $L^2$ norm is at most $\|e_{1/2}\|_2+\|e_2\|_2=O(N^{-15})$ by the same proposition. Proposition 8.1 gives the $O(N^{-13})$ ordering error. Conditional on the hidden weights, the initial readouts are centered, so $\mathbb{E}X=1$. Taking expectations in the identity yields $|\mathbb{E}\Delta-c_N/N^2|=O(N^{-15})$ by Cauchy–Schwarz. Inserting the expansion of $c_N$ gives the signed mean formula. [Proposition 7.2](#projection-fitting-and-exceptional-seeds) · [Proposition 8.1](#ordering-across-all-seeds) · [Corollary 8.3](#the-limiting-coefficient-and-the-signed-shift)

$\square$

**Lean proof.** [Joint fitting and tracking](../formal/CirclePairedTheorem.lean#L41) · [Unconditional tracking and ordering](../formal/CirclePairedTheorem.lean#L209) · [Signed expectation](../formal/CirclePairedTheorem.lean#L264) · [Second-order RMS constant](../formal/CirclePairedSecondOrder.lean#L93)

**What the two ordering rates measure.** For the paired unit-step result each initialization event is obtained using second-moment bounds with failure budget $N^{-1/2}$, and the small-score band is chosen at the same scale. For flow, exponential bounds on Gaussian sums give polynomially small exceptional sets of arbitrarily high fixed order. Integrating over a random readout direction also controls the dependence of the score on the tracking error and removes a logarithmic factor from the final ordering bound. These proofs yield $O(N^{-1/2})$ and $O(N^{-13})$, respectively. They leave open the sharp rates for either algorithm. [GD initialization](../formal/CirclePositiveConfidence.lean#L165) · [GD sign transfer](../formal/CirclePairedGDEndpoint.lean#L49) · [Flow ordering bound](../formal/CirclePairedOrdering.lean#L573)

> **Corollary 3.1 (Prediction from initialization).** For either training rule,
>
> $$
> Y_{1/2}-Y_2=\frac{\pi^2}{40}\frac{1-Q_N f_0}{N^2}+o_p(N^{-2}).
> $$
>
> Fix $0<\gamma\le \Gamma<\infty$. On the corresponding theorem’s fitting and tracking event, whenever $\gamma\le |X|\le \Gamma$, the sign of $\Delta$ is the sign of $X$ and $|\Delta|$ has order $N^{-2}$ for all sufficiently large $N$. The two fitted predictions differ by at most $2N^{-3}$ in grid RMS.

**Proof idea.** A deficit bounded away from zero gives the reference gap a fixed sign and a size bounded below on the $N^{-2}$ scale. The tracking error is smaller on this scale.

**Proof.** Theorem 2 gives the expansion for GD. For flow, Theorem 3 gives $N^2\Delta-c_NX\to0$ in $L^2$. Since $\|X\|_2\le\sqrt{3/2}$ and $c_N\to\pi^2/40$, replacing $c_N$ by its limit preserves $L^2$ convergence and hence convergence in probability. On the fitting and tracking event of either theorem, $|N^2\Delta-c_NX|\le c_N\gamma/2$ eventually because the left side is uniformly $o(1)$ there and $c_N$ tends to a positive constant. For $\gamma\le|X|\le \Gamma$ this forces equal signs and bounds $N^2|\Delta|$ between $c_N\gamma/2$ and $c_N(\Gamma+\gamma/2)$. The grid RMS discrepancy is at most the sum of the two fitting errors.

$\square$

**Lean proof.** [Discrete limiting prediction](../formal/CirclePairedGDTheorem.lean#L47) · [Flow limiting prediction](../formal/CirclePairedTheorem.lean#L221) · [Discrete joint event](../formal/CirclePairedGDTypical.lean#L208) · [Fixed-band flow bounds](../formal/CirclePairedTheorem.lean#L185)

### Varying the hidden-layer rate

At every odd $N\ge3$, $c_N(\tau,\sigma)>0$ for $0\le\tau<\sigma$ and
$$
\lim_{N\to\infty} c_N(\tau,\sigma)=\frac{\pi^2}{12}
\left(\frac{\sigma}{2+\sigma}-\frac{\tau}{2+\tau}\right).
$$
The limiting slopes for $1/2$ to $1$ and $1$ to $2$ are $\pi^2/90$ and $\pi^2/72$, respectively. For $1/2\le\tau<\sigma\le2$ and two endpoint-measurable flows on the same Gaussian seed, at width $N^{32}$ and horizon $H$, the RMS error of $N^2(Y_\tau-Y_\sigma)-c_N(\tau,\sigma)X$ is at most $2C/\sqrt N$ for odd $N\ge33$. Here $C$ is the single-rate tracking constant, independent of the rates and the selected flows. Consequently the error tends to zero in probability. At one fixed rate $r\in[1/2,2]$, $N^2(Y_r-1)$ converges in law to a Gaussian with mean $-\pi^2r/[12(2+r)]$ and variance $(\pi^2/360)[1+5r^2/(2+r)^2]$. [Positivity](../formal/CircleRateDial.lean#L24) · [Limit](../formal/CircleRateDial.lean#L28) · [Common-seed flow](../formal/CircleRateDial.lean#L93) · [Single-rate Gaussian law](../formal/CircleGaussianLimit.lean#L133)

For odd $N\ge36{,}865$, the RMS error of the scaled two-rate prediction is at most $2C_{\rm tr}/N^{13}$, uniformly in the chosen multipliers. Moreover, for every fixed nonnegative integer $k$ and $N\ge k+17$ above this cutoff, one event of probability at least $1-34/N^k$ guarantees that both copies fit and each endpoint satisfies $|Y_r-Z_r|\le(1+176\pi^2)/N^3$. The event works for every compatible flow path from each seed it contains. [Sharp two-rate RMS bound](../formal/CircleRateDial.lean#L138) · [Simultaneous fitting](../formal/CircleRateDial.lean#L158)

With independent seeds, even two copies of the *same* learner exhibit a random difference. At widths tending to infinity, if the reference tracking error is $o(\sqrt{V_N})$ outside an event of vanishing probability, the difference divided by $\sqrt{2V_N}$ converges in law to a standard normal. Here $V_N$ is the single-copy reference variance. This statement uses the product seed law. [Independent trained copies](../formal/CircleWeakPrediction.lean#L129)

At equal rates the flow moment limits hold more broadly. Along growing odd grids, at any widths $m\ge N^{16}$ and physical times $\pi^2\log N\le T\le H$, $N^2(\mathbb EY-1)\to-\pi^2/36$ and $N^4\operatorname{Var}Y\to7\pi^2/1620$ for every admissible measurable selection. [Equal-rate flow moment limits](../formal/CircleBroadFlow.lean#L134)

## Finite-width experiments

For each of four designs we trained the two flow learners from 48 Gaussian draws and 48 independent draws from the Gaussian law conditional on $X<0$. The latter sample uses rejection before training. It tests the prediction that the slower learner can finish with the smaller population mean. The two learners within each pair share all initial parameters. Across widths the unconditional draws use common random numbers: for each seed the smaller network uses the first $m$ neurons of the larger one. At width 8,192 the unconditional $N=3$ and $N=5$ designs use identical initial parameters. Rejection can select different attempts at different widths in the conditional sample. [Integrator and data](../layer-rates/README.md)

Heun's explicit trapezoidal rule recomputes both gradients and gates at the provisional state. The primary runs use step $h=1/4$ to time 160 for $N=3$ and 512 for $N=5$. The theorem horizons are 1,027 and 3,735, respectively. [Exact horizon calculations](../formal/CircleFiniteHorizons.lean#L62)

![The initial deficit $X$ and measured population gap $N^2\Delta$ for 96 pairs at $N=3$, $m=32{,}768$ and time 160, with $N^2=9$. The finite-grid prediction has slope $c_3=0.239159$. The right panel enlarges the neighborhood of a tie. Vertical bars show the largest step-halving change measured in each sampling group.](paired-ordering.png)

At width 32,768 the sign of $X$ predicts all 48 unconditional orderings. Always predicting a larger mean for the slower learner succeeds 45 times. In the conditional sample, where this prediction reverses, the faster learner finishes higher in 46 pairs. Both misses have initial grid means within 0.005 of one. For one ordinary seed with $Q_Nf_0=-0.06839$, the predicted scaled gap is $+0.25551$ and the measured gap is $+0.25300$. At $Q_Nf_0=1.11761$, these values are $-0.02813$ and $-0.02871$. Lean verifies the sign counts by arithmetic on the recorded decimals. The simulation is a numerical computation. [Checked sign counts](../formal/CirclePairedData.lean#L114)

**Table 2.** Correct sign predictions out of the eligible pairs, with exact 95% binomial intervals for the success probability. The margin subset has $\lvert X\rvert\ge0.1$. A tie counts as a miss. G denotes the Gaussian sample and C the Gaussian sample conditional on $X<0$.

| $N$ | $m$ | Law | All pairs (95% interval) | Margin subset (95% interval) |
| --- | ---: | :---: | --- | --- |
| 3 | 512 | G | 47/48 (0.889, 0.999) | 46/46 (0.923, 1.000) |
| 3 | 512 | C | 39/48 (0.674, 0.911) | 19/22 (0.651, 0.971) |
| 3 | 8,192 | G | 48/48 (0.926, 1.000) | 46/46 (0.923, 1.000) |
| 3 | 8,192 | C | 46/48 (0.857, 0.995) | 25/25 (0.863, 1.000) |
| 3 | 32,768 | G | 48/48 (0.926, 1.000) | 46/46 (0.923, 1.000) |
| 3 | 32,768 | C | 46/48 (0.857, 0.995) | 33/33 (0.894, 1.000) |
| 5 | 8,192 | G | 47/48 (0.889, 0.999) | 46/46 (0.923, 1.000) |
| 5 | 8,192 | C | 44/48 (0.800, 0.977) | 26/26 (0.868, 1.000) |

**Table 3.** Through-origin slope $\widehat\beta=\sum XN^2\Delta/\sum X^2$ on all 48 pairs per design and law, with its 95% percentile interval from 4,096 within-sample pair bootstrap replicates. RMS error is measured against $c_N X$. [Full summary](../layer-rates/paired-summary.csv)

| $N$ | $m$ | Law | Slope (95% interval) | RMS error |
| --- | ---: | :---: | --- | ---: |
| 3 | 512 | G | 0.1760 (0.1671, 0.1842) | 0.06942 |
| 3 | 512 | C | 0.2032 (0.1689, 0.2338) | 0.03439 |
| 3 | 8,192 | G | 0.2231 (0.2196, 0.2266) | 0.01860 |
| 3 | 8,192 | C | 0.2367 (0.2288, 0.2457) | 0.00642 |
| 3 | 32,768 | G | 0.2310 (0.2299, 0.2321) | 0.00931 |
| 3 | 32,768 | C | 0.2323 (0.2277, 0.2363) | 0.00428 |
| 5 | 8,192 | G | 0.2140 (0.2097, 0.2182) | 0.03302 |
| 5 | 8,192 | C | 0.2160 (0.1885, 0.2405) | 0.01700 |

For the three unconditional $N=3$ samples, $c_3-\widehat\beta$ is 0.06317, 0.01606 and 0.00816 in order of increasing width. The six-width sweep below tests how the decay changes across a wider range of widths and grids. Work on finite-width tangent kernels studies corrections to the infinite-width dynamics [@hanin2020; @dyer2020; @huang2020; @roberts2022]. Here we measure the shortfall directly from paired trajectories.

**Table 4.** Changes in $N^2\Delta$ under step halving, in units of $10^{-4}$. Each entry gives the RMS and maximum absolute change across the prespecified seeds. The first comparison uses eight seeds per row, the second the first three of those eight. All 88 comparisons preserve the sign. [Refinement data](../layer-rates/paired-refinement.csv)

| $N$ | $m$ | Law | $1/4\to1/8$ (RMS, max) | $1/8\to1/16$ (RMS, max) |
| --- | ---: | :---: | ---: | ---: |
| 3 | 512 | G | 8.941, 22.687 | 4.847, 8.222 |
| 3 | 512 | C | 1.958, 3.191 | 1.808, 3.073 |
| 3 | 8,192 | G | 1.126, 2.532 | 0.586, 0.854 |
| 3 | 8,192 | C | 0.767, 1.774 | 0.494, 0.703 |
| 3 | 32,768 | G | 0.209, 0.545 | 0.087, 0.124 |
| 3 | 32,768 | C | 0.456, 0.891 | 0.072, 0.121 |
| 5 | 8,192 | G | 2.082, 4.018 | 0.928, 1.584 |
| 5 | 8,192 | C | 1.724, 3.389 | 0.452, 0.709 |

ReLU gate crossings affect the order of integration. Across the 24 design, seed and sampling-law combinations with all three step sizes, the observed orders $\log_2(\lvert D_h-D_{h/2}\rvert/\lvert D_{h/2}-D_{h/4}\rvert)$ range from $-2.41$ to $7.00$, where $D_h$ denotes the computed $N^2\Delta$. For each design and law we use the largest observed change in Table 4 as an empirical discretization error bar on the scaled gap. At width 32,768 the largest change is $8.91\times10^{-5}$ across both samples, compared with the slope shortfall 0.00816 at a unit deficit. These checks give no uniform bound across seeds or on the error of an individual trajectory. A separate boundary check at step $1/16$ includes all 19 misses in the primary data and preserves each miss. [Boundary checks](../layer-rates/paired-boundary.csv)

Across the 384 primary pairs, the final grid RMS is below $1.43\times10^{-12}$. For exact flow started at a computed endpoint, the continuation bound gives a further scaled change through $H$ below $8\times10^{-10}$. The recorded diagnostic $\mathrm{imbalance\_drift}$ is the maximum over neurons of the absolute change in $a_j^2-\lVert w_j\rVert^2/\tau$. In exact weighted flow, the two terms have equal time derivatives by ReLU homogeneity, the per-neuron form of balancedness for homogeneous networks [@du2018]. [Checked endpoint and continuation inequalities](../formal/CirclePairedResidualData.lean#L83)

### Dependence on width and grid size

We extended the unconditional sample to 3,216 pairs on five grids, using $m=512\cdot4^j$ for $0\le j\le5$. Each grid reuses its seed indices across all six widths, including the 192 overlapping design–seed pairs from the primary unconditional sample. We integrated with Heun step $1/4$ until a block endpoint had grid RMS below $10^{-10}$ or reached $H$. The largest scaled continuation bound from the numerical endpoints was $1.45\times10^{-6}$. For each $N$ we regressed $\log(c_N-\widehat\beta_m)$ on $\log m$. Each of the 4,096 bootstrap replicates resampled seed indices once and used those indices at all six widths. The intervals in Table 5 quantify seed-sampling variability conditional on fitting one power law across all six widths. On an Intel Core Ultra 9 285K CPU with eight worker processes and single-threaded BLAS, the six-width sweep took 144 seconds. Replaying the primary runs with the direct NumPy integrator took 56 seconds and reproduced the recorded outputs byte for byte. [Per-design results](../layer-rates/width-summary.csv) · [Joint bootstrap](../layer-rates/width-trends.csv)

**Table 5.** Fitted exponent and amplitude of the shortfall over six widths. The last column gives the observed shortfall at the largest width.

| $N$ | Seeds per width | $\widehat\alpha$ (95% interval) | $\widehat\kappa$ (95% interval) | Shortfall at $m=524{,}288$ |
| ---: | ---: | --- | --- | ---: |
| 3 | 200 | 0.469 (0.452, 0.485) | 1.07 (0.90, 1.25) | 0.00228 |
| 5 | 128 | 0.439 (0.420, 0.459) | 1.68 (1.38, 2.04) | 0.00512 |
| 7 | 96 | 0.419 (0.399, 0.438) | 1.98 (1.64, 2.39) | 0.00746 |
| 9 | 64 | 0.406 (0.381, 0.431) | 2.21 (1.69, 2.84) | 0.00983 |
| 11 | 48 | 0.397 (0.371, 0.424) | 2.43 (1.85, 3.21) | 0.01213 |

![Shortfall in the fitted slope across six widths. Lines fit $\kappa m^{-\alpha}$. Bars through the markers give 95% seed-bootstrap intervals. The bars just to their right show the slope sensitivity obtained by applying the largest measured step-halving change to each response. Three fixed seeds per design were repeated at step $1/8$.](../layer-rates/width-scaling.png)

The slope shortfall shrinks with width on every grid. The fitted amplitude increases and the fitted exponent decreases as the grid grows from three to eleven nodes. To place the widths on the scale of the observable, the first tested width whose estimated slope reached $0.95c_N$ was 32,768 at $N=3$, 131,072 at $N=5$, and 524,288 at $N=7,9,11$. These are sample estimates for this statistic.

**Table 6.** Local exponent $\log(S_m/S_{4m})/\log4$, where $S_m=c_N-\widehat\beta_m$. Columns give the lower width $m$. Brackets give pointwise 95% percentile intervals from the same 4,096 joint-seed replicates as Table 5. [Adjacent-width estimates](../layer-rates/width-local-exponents.csv)

| $N$ | 512 | 2,048 | 8,192 | 32,768 | 131,072 |
| ---: | --- | --- | --- | --- | --- |
| 3 | 0.46 [0.38, 0.54] | 0.48 [0.40, 0.56] | 0.47 [0.39, 0.55] | 0.49 [0.43, 0.55] | 0.42 [0.36, 0.49] |
| 5 | 0.41 [0.31, 0.51] | 0.43 [0.35, 0.51] | 0.44 [0.36, 0.53] | 0.47 [0.40, 0.54] | 0.43 [0.35, 0.51] |
| 7 | 0.38 [0.28, 0.48] | 0.36 [0.27, 0.44] | 0.40 [0.31, 0.49] | 0.51 [0.43, 0.59] | 0.45 [0.38, 0.52] |
| 9 | 0.31 [0.18, 0.45] | 0.40 [0.27, 0.53] | 0.36 [0.25, 0.48] | 0.51 [0.42, 0.59] | 0.43 [0.32, 0.53] |
| 11 | 0.22 [0.04, 0.40] | 0.36 [0.24, 0.50] | 0.41 [0.27, 0.55] | 0.52 [0.39, 0.64] | 0.41 [0.30, 0.51] |

At $N=3$, four of five local intervals contain $1/2$, and $\sqrt m\,S_m$ increases from 1.30 to 1.65. At $N=7,9,11$, the local exponents rise from 0.22–0.38 in the first width interval to 0.51–0.52 between 32,768 and 131,072 neurons. They fall in the final interval on all five grids. The grids share initial networks, so these declines are dependent. Across the 30 designs, the step-halving sensitivity measured on three seeds is at most 2.3% of the shortfall. The data resolve changes over these finite widths and leave the asymptotic exponent open.

### Optimizer and initialization controls

We also ran paired unit-step GD to update $H$ on 24 common Gaussian seeds at each of the two primary grid sizes at widths 512 and 8,192. The ordering agreed with $X$ on 24 of 24 seeds at each width for $N=3$ and on 23 of 24 at each width for $N=5$. For $N=3$, the fitted unit-step slopes are 0.172 and 0.219 at widths 512 and 8,192 (24 seeds per width). Flow gives 0.183 and 0.222 on those same 24 seeds, and 0.176 and 0.223 on all 48 primary seeds (Table 3). In the equal-rate capped comparison, $\eta_*=1$ on all 96 of these design–seed pairs and the endpoints coincided with equal-rate unit-step GD. In a separate small-width check at $N=3,m=8$, the cap activated on 3 of 128 natural seeds. The largest absolute change in the endpoint population mean was 0.0192. These runs measure ordinary seeds and give little information about the tail integral in the divergence theorem. [Control results](../layer-rates/control-summary.csv)

For the initialization control we drew $m/2$ Gaussian neurons and included each hidden vector twice, with opposite readouts [@zhang2020]. The initial function vanishes identically, so $X=1$. In 24 paired flow runs per design, the slow copy finished higher in all 96 cases. At widths 512 and 8,192 the respective mean scaled gaps were 0.197 and 0.227 on the three-point grid ($c_3=0.239$), and 0.171 and 0.228 on the five-point grid ($c_5=0.244$). [Initializations and updates](../layer-rates/width_sweep.py)

## Discrete gradient descent on typical initializations

Fix either hidden step $\tau\in\{1/2,2\}$, with readout step one. Write $b=b_{\tau,N}$, so $0\le b\le1$ and $Z_\tau=Qf_0+bX$. Write $r_t=(f_t(x_i)-y_i)_{i=1}^N$ for the grid residual and $\|r_t\|_N^2=N^{-1}\sum_i r_{t,i}^2$. We use the unit-step spectral bound $\|I-K_\tau\|\le1-g_\tau$, where $K_\tau$ includes the grid normalization $1/N$ and $g_\tau=\tau/(\pi N)^2$. The operator norm is induced by $\|\cdot\|_N$. We will compare one actual update with $I-K_\tau$ even when a hidden unit changes its activation during the step. [Unit-step spectral bound](../formal/CirclePositiveSpectrum.lean#L212)

**Where the width enters.** The factor $1/\sqrt m$ controls the size of a single neuron's update and the fluctuations in an empirical kernel entry. Setting $m=N^{32}$ gives $1/\sqrt m=N^{-16}$. In the unit-step proof, allowing $N^4$ times this scale for cumulative motion gives a relative displacement of $N^{-12}$. The kernel perturbation then fits within the $O(N^{-2})$ spectral gap, with enough room to sum the projected changes through $H$. The flow proof takes a radius $32(1+U)/N^{16}$, where $U$ bounds the time integral of the frozen residual. Controlling this integral also controls the error in the population mean. Thus $32$ is an exponent in a sufficient choice of width. [GD parameter inequalities](../formal/CirclePairedGDTypical.lean#L24) · [Flow radius budget](../formal/CircleSharpTracking.lean#L359)

### A bound for the entire trajectory

For the one-rate estimate take

$$
\delta=N^{-1/2},\qquad R_0=\sqrt{12/\delta},\qquad
\rho=N^{-12},\qquad u=160N^{-12},\qquad d_{\tau}=\max(1,\tau).
$$

Let $\kappa=15/[32(\pi N)^2]$ and $\beta=1-\kappa$.

> **Lemma 5.1 (One-rate trajectory estimate).** For every sufficiently large odd $N$, take $m=N^{32}$ and either $\tau\in\{1/2,2\}$. There exists a measurable set $G_\tau$ of initial weights of probability at least $1-\delta$ on which, simultaneously for all integers $t\ge0$,
>
> $$
> \|r_t\|_N\le R_0\beta^t,\qquad
> |Qf_t-Z_\tau|\le N^{-4}+b\|r_t\|_N .
> $$

**Proof idea.** The frozen kernel contracts the residual. If the actual residual has decayed geometrically so far, the accumulated motion of each neuron is small. Only initially near-zero preactivations can change sign during the next update. Their total weight is small enough to preserve the contraction. The projection $Q-bQ_N$ cancels the population update of the frozen kernel, so summing the remaining errors controls the population mean.

**Proof.** For one initial neuron $z=(a,w)$ put $\mathcal E=a^2+\|w\|^2$. Its three coordinates are independent standard normals, so $\mathbb{E} \mathcal E=3$, $\mathbb{E} \mathcal E^2=15$ and $\mathrm{Var}(\mathcal E)=6$. In this initialization calculation the neuron averages use independent draws. Chebyshev gives $\Pr(m^{-1}\sum_j \mathcal E_j>4)\le6/m$. At each grid input $f_0$ is centered and has second moment $1/2$, since the readout is independent of the hidden weight and a standard normal has positive-part second moment $1/2$. The grid average of $y_i^2$ is $3/2$. Thus $\mathbb{E}\|r_0\|_N^2=2$ and $\Pr(\|r_0\|_N>R_0)\le\delta/6$. [Initial residual moment](../formal/CircleInitialResidualSecond.lean#L96)

We also need the energy of neurons whose activation could change under a displacement of size $\rho\sqrt{\mathcal E}$. For a unit input $v$, define $M(v)=\mathcal E\,\mathbf{1}_{\{|w^\top v|\le\rho\sqrt{\mathcal E}\}}$. The direction of $z$ is uniform on the two-dimensional sphere and independent of its radius. Its projection onto $(0,v)$ is uniform on $[-1,1]$ after division by the radius. Hence $\mathbb{E} M(v)=3\rho$ and $\mathbb{E} M(v)^2=15\rho$. Averaging $M(v)$ over the circle preserves its expectation and, by Jensen, gives a second moment at most $15\rho$. For each grid input and for this one angular average, Chebyshev bounds the probability that the neuron average exceeds $6\rho$ by $15\rho/[m(3\rho)^2]$. The probability that any of the $N+1$ bounds fails is at most $5(N+1)/(3m\rho)$. This bound and $6/m$ are each at most $\delta/6$ for sufficiently large $N$ at $m=N^{32}$. [Gaussian margin moments](../formal/CircleInitializationConcentration.lean#L747) · [Simultaneous grid and angular margins](../formal/CircleFiniteConfidence.lean#L152)

Write $h(v,v')$ for the one-neuron contribution to the unnormalized tangent kernel at initialization. With $p(v)=[w^\top v]_+$ and $d(v)=\mathbf{1}_{\{w^\top v>0\}}$ it is

$$
h(v,v')=p(v)p(v')+\tau a^2 d(v)d(v')\,v^\top v'.
$$

Thus $|h|\le d_{\tau} \mathcal E$. Denote the neuron average by $\widehat h$, and its expectation by $h_*$, so $(K_\tau)_{ij}=h_*(x_i,x_j)/N$. Each column also gives an angular row $Qh(\cdot,x_j)$ and a difference of rows $(Q-bQ_N)h(\cdot,x_j)$. The first is bounded by $d_{\tau}\mathcal E$ and the second by $2d_{\tau}\mathcal E$. The expectation of the second is zero by the defining population-to-grid ratio $b$. For a family of $d$ such quantities each bounded by $c_h\mathcal E$, the probability that any neuron average deviates from its expectation by more than $c_h\sqrt{90d/(m\delta)}$ is at most $\delta/6$. Indeed each variance is at most $15c_h^2/m$ and we sum Chebyshev's bound over the family. Apply this to the $N^2$ grid entries, the $N$ angular entries, and the $N$ differences. All three thresholds are at most $u$ for sufficiently large $N$. Together with the residual, energy and margins, these three families give a measurable event $G_\tau$ of probability at least $1-\delta$. The formal proof further sharpens the envelope for the row difference to $d_{\tau}(6/N+1-b)\mathcal E$. [Row cancellation and concentration](../formal/CirclePositiveConfidence.lean#L148) · [Joint event](../formal/CirclePositiveConfidence.lean#L165)

Fix a seed in $G_\tau$. At the specified width the parameters satisfy

$$
\frac{2d_{\tau}R_0}{\sqrt m}\le\rho \kappa,\qquad
36d_{\tau}\rho+u\le g_\tau-\kappa,\qquad
[u+(1+b)36d_{\tau}\rho]R_0/\kappa\le N^{-4}.
$$

For sufficiently large $N$ these follow from $d_{\tau}\le2$, $R_0\le4N$, $1/\kappa\le40N^2$ and $g_\tau-\kappa\ge1/[32(\pi N)^2]$. In particular, the bracket in the third inequality is at most $304N^{-12}$. [Parameter bounds](../formal/CirclePairedGDTypical.lean#L24)

We prove simultaneously that $\|r_t\|_N\le R_0\beta^t$ and that every neuron's displacement from its initial value is at most $\rho(1-\beta^t)\sqrt{\mathcal E_j}$. Both hold at $t=0$. The norm of the update to neuron $j$ is at most $d_{\tau}\|r_t\|_N\|(a_{j,t},w_{j,t})\|/\sqrt m$. This follows by Cauchy–Schwarz in the grid sums for the two layer gradients, using $|[w^\top x]_+|\le\|w\|$ and $\|d(x)x\|\le1$. The displacement hypothesis bounds the current neuron norm by $2\sqrt{\mathcal E_j}$. The first parameter inequality then bounds the extra motion by $\rho \kappa \beta^t\sqrt{\mathcal E_j}$. Every point on the straight update segment, including its endpoint, therefore has displacement at most $\rho(1-\beta^{t+1})\sqrt{\mathcal E_j}$. [Simultaneous update and motion bound](../formal/CircleWeightedStep.lean#L42) · [Induction](../formal/CircleWeightedDynamics.lean#L93)

For $0\le v\le1$, form the mixed kernel $h_{t,v}$ by taking the prediction derivative at the fraction $v$ of this segment and the training-input derivative at its start, with the layer weights $1,\tau$, summed over neurons with the network normalization. Integrating the prediction along the segment gives

$$
r_{t+1}=r_t-\int_0^1 K_{t,v}r_t\,dv,\qquad
(K_{t,v})_{ij}=h_{t,v}(x_i,x_j)/N .
$$

Along a straight segment a hidden preactivation is affine. A crossing has measure zero, and a preactivation identically zero along the segment has zero directional derivative. The integral therefore holds with the prescribed ReLU gate at zero. [Derivative on the update segment](../formal/CircleWeightedStep.lean#L93)

For either input, a changed gate requires the initial preactivation to lie within $\rho\sqrt{\mathcal E_j}$ of zero. The change in a product of two activations is bounded by $(2\rho+\rho^2)\mathcal E_j$, by expanding the product and using the Lipschitz bound for each activation. The product of two readout weights obeys the same estimate. Changing the two gates in the remaining initial product costs at most $\mathcal E_j$ times the sum of their two margin indicators. Summing these bounds gives

$$
|h_{t,v}(x_i,x_j)-\widehat h(x_i,x_j)|
\le d_{\tau}[(4\rho+2\rho^2)4+12\rho]\le36d_{\tau}\rho .
$$

The identical estimate holds after averaging the first input over the circle, using the angular margin bound. If all entries of an unnormalized kernel error have magnitude at most $e$, each coordinate of its normalized action on $r$ is bounded by $eQ_N|r|\le e\|r\|_N$. It follows that $\|K_{t,v}-K_\tau\|\le36d_{\tau}\rho+u$. Applying the reference contraction and the second parameter inequality now gives $\|r_{t+1}\|_N\le(1-g_\tau+36d_{\tau}\rho+u)\|r_t\|_N\le \beta\|r_t\|_N$. This closes the induction and yields $\sum_{t\ge0}\|r_t\|_N\le R_0/\kappa$. [Mixed-kernel drift](../formal/CircleTangentDrift.lean#L205) · [Discrete contraction](../formal/CircleWeightedDynamics.lean#L93)

Apply $Q-bQ_N$ to the same segment identity for the prediction. At initialization each resulting kernel column has magnitude at most $u$. At every intermediate point its change is at most $(1+b)36d_{\tau}\rho$ by the two drift bounds. Each step therefore changes $(Q-bQ_N)f_t$ by at most $[u+(1+b)36d_{\tau}\rho]\|r_t\|_N$. Summation and the third parameter inequality bound the total change by $N^{-4}$. Since $Q_N y=1$, we have

$$
Qf_t-Z_\tau=(Q-bQ_N)(f_t-f_0)+bQ_N r_t ,
\qquad |Qf_t-Z_\tau|\le N^{-4}+b\|r_t\|_N .
$$

$\square$

**Lean proof.** The initialization event is [six_tests](../formal/CirclePositiveConfidence.lean#L165). The [projected increment](../formal/CircleWeightedStep.lean#L184) and the discrete induction yield [unit_trajectory](../formal/CircleWeightedDynamics.lean#L239). The [parameter inequalities](../formal/CirclePairedGDTypical.lean#L24) give the stated powers of $N$.

### The paired endpoint

> **Proposition 5.2 (Paired endpoint and ordering).** At the common unit-step endpoint $H$ and width $N^{32}$, for all sufficiently large odd $N$, an event of probability at least $1-2/\sqrt N$ gives simultaneous fitting and $|N^2\Delta-c_N X|\le10N^{-33/32}$. The probability of $\Delta X\le0$ is $O(N^{-1/2})$, and $N^2\Delta-(\pi^2/40)X$ converges to zero in probability.

**Proof idea.** The two copies share the exact same initial deficit. Subtract their one-rate estimates and the initial population means cancel. A sign error is then possible only on the exceptional set or when the initial grid mean lies very close to one.

**Proof.** At the prescribed horizon $H$, the inequality $1-\kappa\le e^{-\kappa}$ gives

$$
R_0\beta^H\le \sqrt{12}\,N^{1/4}(2\sqrt{12}\,N^{7/2})^{-15/16}
\le4N^{-97/32}.
$$

The sufficient cutoff $N\ge4^{32}$ makes this at most $N^{-3}$. The unscaled population error is at most $5N^{-97/32}$. Intersect the two events $G_{1/2}$ and $G_2$ for the *same* Gaussian draw. Their intersection has probability at least $1-2/\sqrt N$. There both runs fit. Writing $\Delta=Y_{1/2}-Y_2$ and using $Z_{1/2}-Z_2=c_NX/N^2$, we obtain $|N^2\Delta-c_NX|\le10N^{-33/32}$. [Horizon estimate](../formal/CirclePairedGDClock.lean#L52) · [Paired event](../formal/CirclePairedGDTypical.lean#L208)

Finally, condition on the initial hidden weights. The initial grid mean is a centered Gaussian linear combination of independent readouts. At any $x\ge1/2$, maximizing its density over all positive standard deviations gives the uniform upper bound $d_{\rm G}=2e^{-1/2}/\sqrt{2\pi}$, attained at $x=1/2$ and standard deviation $1/2$. A zero-variance conditional law is concentrated at zero. Integrating the conditional bound gives $\Pr(|X|\le v)\le2d_{\rm G}v$ for $0\le v\le1/2$. Since $c_N\to\pi^2/40>0$, eventually $10N^{-33/32}<c_N/\sqrt N$. On the paired event the sign is therefore correct whenever $|X|>N^{-1/2}$. Counting ties as misses gives probability at most $(2+2d_{\rm G})/\sqrt N$. [Uniform Gaussian band](../formal/CircleScoreMargin.lean#L89) · [Sign transfer](../formal/CirclePairedGDEndpoint.lean#L49)

For the magnitude, Jensen gives $\mathbb{E} X^2\le1+Q_N\mathbb{E} f_0^2=3/2$. For any fixed $\varepsilon>0$, take $N$ large enough that $10N^{-33/32}<\varepsilon/2$. The probability that $|N^2\Delta-(\pi^2/40)X|\ge\varepsilon$ is then at most $2/\sqrt N+4|c_N-\pi^2/40|^2\mathbb{E} X^2/\varepsilon^2$, by the triangle inequality and Markov's inequality. This tends to zero.

$\square$

**Lean proof.** The shared fitting and tracking event is [common_event](../formal/CirclePairedGDTypical.lean#L208). The sign and magnitude conclusions are [fit_and_order](../formal/CirclePairedGDTheorem.lean#L36) and [limiting_prediction](../formal/CirclePairedGDTheorem.lean#L47).

## Mean-square divergence for discrete gradient descent

Take odd $N\ge3$ and $m\ge1$. Allow any fixed readout step $\eta>0$ and hidden step $\eta\tau$, with $\tau=1/2$ or $2$. Both networks start from the same Gaussian draw. At update $T$, write $Y_{\tau,T}=Qf_{\tau,T}$ and $\Delta_T=Y_{1/2,T}-Y_{2,T}$. We will find a single set of seeds where the **difference** between the two means is large. Large individual means alone need not give a large difference from a shared seed. The expectation includes every seed at the prescribed endpoint, including runs that miss the fitting tolerance.

### A common box of escaping trajectories

Choose $R_{\eta}\ge32$ with $R_{\eta}^2\ge16(32/\eta+32)$. At unit step $R_{\eta}=32$ suffices. Let $z^*$ be the seed with $a_j=R_{\eta}$ and $w_j=(R_{\eta},0)$ for every neuron. For an integer $T\ge2$ set $\ell=(8N\,512^{2T})^{-1}$ and define $E_T=z^*+[0,\ell]^{3m}$.

> **Lemma 6.1 (Separation on a common box).** For every odd $N\ge3$, every $m\ge1$, every $\eta>0$ and every $T\ge2$, each seed in $E_T$ satisfies $|\Delta_T|\ge\sqrt m\,2^{3^{T-1}}$.

**Proof idea.** At the symmetric seed $z^*$ the two networks reduce to scalar iterations whose signs alternate together. The ratio of the fast and slow readout–hidden products grows at least cubically because the fast copy takes the larger hidden step. The odd grid leaves a positive margin at every activation, which lets a common neighborhood follow both scalar iterations long enough for their population means to separate.

**Proof.** Start at $z^*$. Write $s=(-1)^t$ at step $t$. We claim that all neurons within either run then have $a_j=sA$ and $w_j=(sW,0)$ for positive magnitudes $A,W\ge R_{\eta}$ that may differ between runs.

To compute the next step, define $h_s(u)=[s\cos u]_+$, $q_s=Q_Nh_s^2$, and $b_s=Q_N(yh_s)$. The grid averages of $\cos u$ and $\cos^2 u$ are zero and $1/2$, respectively. Hence $Q_Nh_s=\tfrac12Q_N|\cos u|\ge\tfrac12Q_N\cos^2u=1/4$, and Jensen's inequality gives $q_s\ge1/16$. Also $0\le b_s\le2$ since $0\le y\le2$ and $0\le h_s\le1$. [Grid feature bounds](../formal/CircleGridMargin.lean#L61) · [Bounds for the label term](../formal/CirclePairedGDGeometry.lean#L41)

The residual at angle $u_i$ is $\sqrt m\,sAW h_s(u_i)-y_i$. Reflection $i\mapsto-i$ preserves the residual, $\cos u_i$, and the ReLU gate $\mathbf 1_{\{s\cos u_i>0\}}$, while reversing $\sin u_i$. Thus the vertical hidden derivative sums to zero. The horizontal derivative uses $\cos u_i\,\mathbf 1_{\{s\cos u_i>0\}}=s h_s(u_i)$. Writing $r$ for that residual, the readout increment is $-\eta W Q_N(rh_s)/\sqrt m$, and the horizontal increment is $-\eta\tau A Q_N(rh_s)/\sqrt m$. Both use $Q_N(rh_s)=\sqrt m\,sAWq_s-b_s$. Set $\beta=s b_s/\sqrt m$ and $q=q_s$. These identities give the next signed readout and horizontal weight as $-sA'$ and $-sW'$, where

$$
\begin{aligned}
A'&=\eta q AW^2
\left(1-\frac{1}{\eta q W^2}-\frac{\beta}{qAW}\right),\\
W'&=\eta\tau q A^2W
\left(1-\frac{1}{\eta\tau q A^2}-\frac{\beta}{qAW}\right).
\end{aligned}
$$

Since $\tau\ge1/2$ and $|\beta|\le2$, each parenthesis differs from one by at most $(32/\eta+32)/R_{\eta}^2\le1/16$. Moreover $\eta R_{\eta}^2\ge512$, so $A'\ge2A$ and $W'\ge2W$. This proves the claimed sign and lower magnitude bounds by induction, starting with $A=W=R_{\eta}$. [Simultaneous update](../formal/CirclePairedGDGeometry.lean#L112) · [Magnitude growth](../formal/CirclePairedGDScalar.lean#L81) · [Identification with the network iterates](../formal/CirclePairedGDCenter.lean#L160)

For each run let $P_{\tau,t}=A_{\tau,t}W_{\tau,t}$ and let $D_t=P_{2,t}/P_{1/2,t}$. Multiplying the two recursions puts $P_{\tau,t+1}$ between $(15/16)^2$ and $(17/16)^2$ times $\eta^2\tau q_s^2P_{\tau,t}^3$. Both runs have the same $s$ at each step. Dividing cancels $q_s^2$ and yields

$$
D_{t+1}\ge 4(15/17)^2D_t^3\ge2D_t^3,\qquad
D_T\ge2^{1+3+\cdots+3^{T-1}}=2^{(3^T-1)/2}
$$

for $T\ge1$, since $D_0=1$. The shared sign thus gives a lower bound on the relative growth of the two actual trajectories. [One-step ratio](../formal/CirclePairedGDScalar.lean#L145) · [Iterated ratio](../formal/CirclePairedGDCenter.lean#L91)

The symmetric initialization has Gaussian probability zero. Around each run's symmetric state, measure the readout error coordinatewise in units of $A$ and each of the two hidden-coordinate errors in units of $W$. Suppose all three relative errors are at most $e\le1/(8N)$ for every neuron. A hidden dot product changes by at most $2eW$. Its magnitude at a grid point in the symmetric state is at least $W/N$. Indeed, for $v=\pi/2-u_i$, oddness of $N$ gives $|\sin(Nv)|=1$, and the sine addition formula gives $|\sin(Nv)|\le N|\sin v|=N|\cos u_i|$. All perturbed gates therefore agree with the symmetric gates at the beginning of this update. [Odd-grid clearance](../formal/CirclePairedGDGeometry.lean#L64) · [Gate equality](../formal/CirclePairedGDTube.lean#L113)

ReLU changes by at most the change in its argument. Its perturbed value is at most $3W$ and differs from the symmetric value by at most $2eW$. A readout-feature product consequently changes by at most $(eA)(3W)+A(2eW)=5eAW$. Summing the $m$ terms with the network normalization bounds the residual change by $5e\sqrt m\,AW$. The symmetric residual has magnitude at most $\sqrt m\,AW+2\le3\sqrt m\,AW$. [Output perturbation](../formal/CirclePairedGDTube.lean#L101)

For one parameter coordinate, let $L_{\rm opp}=W$ for a readout and $L_{\rm opp}=A$ for a hidden weight. After taking out $m^{-1/2}$, the output derivative in that coordinate is either an activation or a readout times a gate and one input coordinate. Its perturbed magnitude is at most $3L_{\rm opp}$, and its change is at most $2eL_{\rm opp}$ because the gates agree. Multiplying by the residual, the corresponding gradient summand changes by at most

$$
(5e\sqrt m\,AW)(3L_{\rm opp})+(3\sqrt m\,AW)(2eL_{\rm opp})=21e\sqrt m\,AWL_{\rm opp}.
$$

The grid average preserves the bound, and the gradient normalization cancels $\sqrt m$. Set $M=\eta AW^2$ for a readout or $M=\eta\tau A^2W$ for a hidden coordinate. If $U$ denotes the old layer magnitude and $U'$ its next symmetric magnitude, the next absolute error is at most $eU+21eM$. The recursion above gives $U\le M$ and $U'\ge(15/256)M\ge M/32$. Thus the next relative error is at most $1024e$. [Gradient difference](../formal/CirclePairedGDTube.lean#L178) · [One-step relative error](../formal/CirclePairedGDTube.lean#L234)

For seeds in the box $E_T$, each initial coordinate differs from its symmetric value by at most $\ell$. Since $512^2\ge1024$ and $R_{\eta}\ge1$, the initial relative error in either run is at most $1/(8N\,1024^T)$. At step $t\le T$ it is at most $1024^{t-T}/(8N)$. This induction preserves the gate condition through the final step. The same box works for the two runs. [Initial box](../formal/CirclePairedGDCoordinates.lean#L15) · [Induction through the endpoint](../formal/CirclePairedGDShadow.lean#L23)

Write $s=(-1)^T$ and use $A,W$ for either run's final symmetric magnitudes. The bound $e\le1/8$ puts $sa_j$ between $7A/8$ and $9A/8$. The first hidden coordinate gives $\|w_j\|\ge7W/8$ and the sum of absolute coordinates gives $\|w_j\|\le10W/8$. Inserting these bounds into $Y_{\tau,T}=(\pi\sqrt m)^{-1}\sum_j a_j\|w_j\|$ gives

$$
\frac{\sqrt m}{2\pi}P_{\tau,T}\le sY_{\tau,T}\le
\frac{2\sqrt m}{\pi}P_{\tau,T}.
$$

For $T\ge2$, the ratio bound gives both $P_{2,T}\ge8P_{1/2,T}$ and $P_{2,T}\ge2^{3^{T-1}}P_{1/2,T}$. Subtract the upper bound for the slow run from the lower bound for the fast run. Since $P_{1/2,T}\ge R_{\eta}^2\ge4\pi$, every seed in $E_T$ satisfies

$$
|\Delta_T|\ge s(Y_{2,T}-Y_{1/2,T})
\ge\frac{\sqrt m}{4\pi}P_{2,T}
\ge\sqrt m\,2^{3^{T-1}}.
$$

$\square$

**Lean proof.** The exact trajectories are [iterate_center](../formal/CirclePairedGDCenter.lean#L160), their relative growth is [ratio_growth_exact](../formal/CirclePairedGDCenter.lean#L91), and the common-neighborhood estimate is [shadow](../formal/CirclePairedGDShadow.lean#L23). The signed population comparison gives [box_contrast_scaled](../formal/CirclePairedGDBox.lean#L138).

### Gaussian mass and squared prediction error

> **Proposition 6.2 (Divergence of the squared prediction error).** Fix $\eta>0$. Along any sequence of odd grids $N\ge3$, widths $m\ge1$ and integer times $T$ such that $3^T/[m(T+\log N+1)]\to\infty$, every bounded deterministic coefficient sequence $d$ satisfies
>
> $$
> \mathbb{E}\!\left[(\Delta_T-dX/N^2)^2\right]\longrightarrow\infty .
> $$
>
> Each expectation is finite at every finite width and time. With $m=N^{32}$ and odd $N\to\infty$, the conclusion holds at $T=\lceil60\log N\rceil$, $T=H$ and $T=\lceil H/\eta\rceil$.

**Proof idea.** Squaring the separation in Lemma 6.1 gives a term whose logarithm grows like $3^T$. The negative logarithm of the box probability grows only as $m(T+\log N+1)$. The predictor has uniformly bounded second moment, so subtracting it preserves divergence.

**Proof.** Every coordinate in the box has magnitude at most $R_{\eta}+1$. Its standard Gaussian density is therefore at least $(2\pi)^{-1/2}\exp[-(R_{\eta}+1)^2/2]$. Multiplication of the $3m$ interval probabilities gives $\Pr(E_T)\ge e^{-C}$, where

$$
C=3m\left[\frac{(R_{\eta}+1)^2}{2}+\log(8\sqrt{2\pi}\,N)+2T\log 512\right].
$$

For fixed $\eta$, choose $R_{\eta}$ once so that $C\le C_\eta m(T+\log N+1)$ with a constant independent of $N,m,T$. Squaring the contrast bound, integrating over $E_T$, and using $m\ge1$ yields $\mathbb{E}[\Delta_T^2]\ge\exp[(2\log 2/3)3^T-C]$. [Gaussian box mass](../formal/CircleSynchronizedWidth.lean#L59) · [Uniform cost bound](../formal/CirclePairedGDCost.lean#L38) · [Integral lower bound](../formal/CirclePairedGDTail.lean#L33)

Every finite iterate has finite moments of every positive finite order. The initial Gaussian coordinates have this property. Sums preserve it, products preserve it by Hölder's inequality, and ReLU and its bounded measurable gate preserve it. Induction over the simultaneous updates gives the claim for all parameters. The angular mean formula preserves finite moments since $\|w_j\|\le |w_{j,1}|+|w_{j,2}|$. In particular, all expectations in the argument are finite at each $T$. [Finite-iterate moments](../formal/CirclePairedGDIntegrable.lean#L116) · [Moments of both observables](../formal/CirclePairedGDIntegrable.lean#L140)

Writing $d_N$ for the bounded coefficient along the sequence, put $G=d_NX/N^2$, where $X=1-Q_Nf_0$. Its second moment is uniformly bounded. To see this, condition on the initial hidden weights. Independence and centering of the readouts give $\mathbb{E}[X^2]=1+\mathbb{E}[(Q_N[w^\top x]_+)^2]$ for a single Gaussian hidden vector $w$. Jensen's inequality bounds the last expectation by $Q_N\big(\mathbb{E}[([w^\top x]_+)^2]\big)=1/2$. The ratio hypothesis forces $T\to\infty$ and makes $C/3^T\to0$, so the integral lower bound gives $\mathbb{E}[\Delta_T^2]\to\infty$. The elementary inequality $\Delta_T^2\le2(\Delta_T-G)^2+2G^2$ transfers divergence to the prediction error. [Uniform predictor bound](../formal/CirclePairedGDIntegrable.lean#L162) · [Mean-square subtraction](../formal/CirclePairedGDIntegrable.lean#L175)

There is also a finite bound. On $E_T$, $|X|\le\sqrt m(2+16R_{\eta}^2)$, as follows by bounding the initial readouts by $R_{\eta}+1$ and the hidden norms by $R_{\eta}+2$. If $|d_N|\le D$ and $D(2+16R_{\eta}^2)\le N^2$, then $|G|\le\sqrt m$ there. For $T\ge2$ this leaves $|\Delta_T-G|\ge 2^{3^{T-1}}/2$, giving $\mathbb{E}[(\Delta_T-G)^2]\ge\tfrac14\exp[(2\log 2/3)3^T-C]$. [Finite prediction-error bound](../formal/CirclePairedGDFiniteTail.lean#L35)

Finally take $m=N^{32}$ and let odd $N$ grow. Under $T\ge60\log N$, the reciprocal of the ratio above is at most $3T\exp[-(\log 3-32/60)T]$ eventually, which tends to zero. The divergence thus holds at $\lceil60\log N\rceil$, at $H$, and at $\lceil H/\eta\rceil$ for every fixed $\eta>0$, since $H/\log N\to\infty$. At $\eta=1$ and $T=H$ this is the very endpoint where joint fitting and the scaled prediction hold with probability tending to one. It covers both the finite-grid coefficient $c_N$ and its limit $\pi^2/40$. [Clock estimate](../formal/CirclePairedGDCost.lean#L79)

$\square$

**Lean proof.** The general criterion is [of_ratio](../formal/CirclePairedGDTail.lean#L97). Its three clock specializations are [at_logarithmic](../formal/CirclePairedGDClocksTail.lean#L56), [at_horizon](../formal/CirclePairedGDClocksTail.lean#L49) and [at_physical_clock](../formal/CirclePairedGDClocksTail.lean#L64).

## Nonlinear tracking for gradient flow

Throughout this section $H$ is the deterministic horizon of the main theorems. We first construct flow paths and bound the motion of their parameters. We then compare the nonlinear residual to its evolution under the fixed tangent kernel.

### Existence and dissipation at ReLU kinks

Write $\theta_j=(a_j,w_j)$ for neuron $j$, $D_\tau$ for the diagonal matrix with entries $(1,\tau,\tau)$ per neuron, $r=f_\theta-y$ on the grid, and $L=\frac12\|r\|_N^2$, where $\|r\|_N^2=N^{-1}\sum_i r_i^2$. Away from zero preactivations, the $j$th block of the output derivative at $x$ is

$$
J(x)_j=m^{-1/2}\big([w_j^\top x]_+,\,a_j g_j(x)x\big),
 \qquad g_j(x)=\mathbf 1_{\{w_j^\top x>0\}}.
$$

At zero allow $g_j(x)\in[0,1]$. Write $\|v\|_{D_\tau^{-1}}^2=v^\top D_\tau^{-1}v$.

> **Lemma 7.1 (Existence and dissipation).** For $N\ge3$, $m\ge1$ and $0<\tau\le2$, there is a Borel map assigning to every initial state a global weighted Clarke flow starting there. Every such flow satisfies, almost everywhere in time,
>
> $$
> \dot L=-\|\dot\theta\|_{D_\tau^{-1}}^2,\qquad
> \frac{d}{dt}\|\theta\|_{D_\tau^{-1}}^2=\|y\|_N^2-4\|f_\theta-y/2\|_N^2.
> $$
>
> In particular $\|\theta(t)-\theta(0)\|^2\le2tL(0)$ for every $t\ge0$.

**Proof idea.** On the zero set of an absolutely continuous preactivation its velocity vanishes almost everywhere. This makes the chain rule compatible with all admissible gate choices. Dissipation controls path length, and the radial identity keeps finite-time solutions in bounded sets.

**Proof.** A valid path has absolutely continuous coordinates and obeys $\dot\theta=-D_\tau J^\top r/N$ almost everywhere for a common admissible set of grid slopes. An actual weighted Clarke flow satisfies this condition. Each strict activation chamber has its ordinary polynomial loss gradient. Its limiting gradient at a boundary point uses the slopes of that chamber. The velocities obtained by convexly mixing incident chamber gradients use the same mixtures of slopes because the velocity is affine in the slopes at fixed $\theta$. The complement of the strict chambers has Lebesgue measure zero, and each incident full-dimensional chamber has positive measure in arbitrarily small neighborhoods. Thus their convex hull gives the essential limiting-gradient field there. [Definition of a valid path](../formal/CircleFlowPath.lean#L189) · [Identification of the Clarke field](../formal/CirclePathSelection.lean#L429)

For an absolutely continuous scalar preactivation $s(t)$, $\dot s=0$ almost everywhere on $\{s=0\}$. At these times every permitted $g$ gives $(s_+)'=g\dot s=0$. Applying this fact to the finite grid yields $\dot r=J\dot\theta$ with the very slopes used in the velocity. Taking the normalized inner product with $r$ and substituting the velocity gives $\dot L=-\|\dot\theta\|_{D_\tau^{-1}}^2$. Since $gs=s_+$ even at zero, $J\theta=2f_\theta$. Pairing $\theta$ with its velocity now gives the radial derivative $-4Q_N[rf_\theta]$, which is the stated difference of squares. Integration and Cauchy–Schwarz yield the displacement estimate, using $\|v\|^2\le2\|v\|_{D_\tau^{-1}}^2$. [Chain rule and loss dissipation](../formal/CircleFlowPath.lean#L216) · [Radial identity](../formal/CircleFlowPath.lean#L257) · [Displacement](../formal/CircleFlowPath.lean#L365)

These estimates also furnish a learner defined from every initial state. On a bounded ball the finite family of chamber velocities is bounded, and its incident hull has nonempty compact convex values and is upper hemicontinuous. Clip the argument of this field to a ball larger than the radial estimate allows the trajectory to reach on $[0,T]$. Piecewise linear approximations for the bounded field have uniformly bounded speeds. A uniformly convergent subsequence satisfies the integrated inequalities against linear functionals that characterize membership of the derivative in the convex velocity set. Up to a first exit the radial estimate applies to this limit, so it stays strictly inside the ball through $T$. On bounded sets of seeds the radius and speed bounds are uniform on each compact time interval. Compactness of the finite-horizon path families and closedness of the integrated inequalities give compatible global paths by taking limits on successive integer time intervals. On a closed ball of seeds, Arzelà–Ascoli and the closed path conditions make the seed–path graph compact in the topology of uniform convergence on compact intervals. For an open set of paths, the seeds admitting a solution in it form a countable union of compact projections, obtained by exhausting the open set by closed subsets and the seed space by closed balls. The solution correspondence thus has measurable open-set preimages and nonempty closed fibers, so it admits a Borel selection. Evaluating that selection at a fixed time yields a measurable endpoint. [Finite-horizon construction and continuation](../formal/CircleLocalContinuation.lean#L120) · [Global Borel Clarke selection](../formal/CircleFlowConstruction.lean#L75)

$\square$

**Lean proof.** The global path is constructed in [exists_borel_global_clarke_flow](../formal/CircleFlowConstruction.lean#L75). The identities and bound are [loss_dissipation](../formal/CircleFlowPath.lean#L238), [radial_derivative](../formal/CircleFlowPath.lean#L257) and [euclidean_displacement](../formal/CircleFlowPath.lean#L365).

### The integrated grid residual

For the tracking argument assume henceforth that $N\ge36865$ is odd, $m=N^{32}$, and $1/2\le\tau\le2$.

With the normalized grid inner product, the actual grid operator is $A_t=JD_\tau J^\top/N$ and $\dot r=-A_t r$. Let $K$ be its deterministic Gaussian expectation at initialization. Rotational invariance makes $K$ circulant. Its eigenvalue $\lambda_r$ in frequency residue $r$ is the sum of the nonnegative tangent Fourier coefficients over that residue. For any nonzero residue on an odd grid there are even representatives $j$ and $j-2N$ with $0<j<2N$. The two coefficients contribute at least $\tau\pi^{-2}(j^{-2}+(2N-j)^{-2})\ge 2\tau/(\pi N)^2$. The constant residue contains the coefficient $(2+\tau)/\pi^2$. Hence $K\succeq\lambda I$ with $\lambda=(\pi N)^{-2}$. Write $u(t)=e^{-tK}r(0)$. Using the gap alone would cost $\|r(0)\|_N/\lambda$ in the integral of $\|u(t)\|_N$. The sharper estimate uses the size of the initial residual *in each decay mode*. [Kernel identification](../formal/CircleKernelIdentification.lean#L539) · [Odd-grid gap](../formal/CircleGridSpectrum.lean#L133) · [Frozen Fourier evolution](../formal/CircleSpectralPathLength.lean#L146)

Let $\alpha_r$ be the normalized discrete Fourier coefficient of $r(0)$. One hidden weight of polar angle $\phi$ contributes a translate of $\|w\|[\cos(\cdot-\phi)]_+$. The angular Fourier coefficients of $[\cos u]_+$ at $k=\pm1$ equal $1/4$. At even $k=2j$ they equal $(-1)^j/[\pi(1-k^2)]$, and the remaining odd coefficients vanish. Sampling sums the absolutely convergent series over grid aliases. Outside residues $0,\pm1$, choose the even representative $k$ with $|k|<N$. Its nonzero aliases have the form $k+2N\ell$. Summing their inverse-square envelope bounds the magnitude of the unit’s grid coefficient by $C\|w\|/(1+|k|)^2$. Multiplication by the independent centered readout gives a centered mark with magnitude at most $C\|\theta_j\|^2/(1+|k|)^2$. The real and imaginary parts of the normalized sum of these independent marks have fourth norm at most the same constant times $(1+|k|)^{-2}$. Indeed, for centered independent real marks, the fourth moment of the $m^{-1/2}$ sum is $m^{-1}\mathbb{E}\xi^4+3(1-m^{-1})(\mathbb{E}\xi^2)^2$. Gaussian energy has the required fourth moment. The formal proof obtains this bound from the centered Gaussian mark moment-generating estimate, which also supplies exponential tails below. The three exceptional residues have bounded fourth norms, including the deterministic teacher coefficients. [Half-wave coefficients](../formal/CircleSpectrum.lean#L44) · [Aliasing bound](../formal/CircleResidualSpectrum.lean#L205) · [Actual residual moments](../formal/CircleResidualSpectrum.lean#L414)

Group residues by $D=2^{\lfloor\log_2(1+|k|)\rfloor}$, using $k=0,\pm1$ in the exceptional residues. Each group $S_D$ has at most $5D$ residues, and each eigenvalue in it is at least $c/D^2$, where $c=1/[32(1+\pi^2)]$. The latter follows by retaining the single even coefficient at $k$ for an ordinary residue and the constant or first coefficient for an exceptional one. If $h_D=(\sum_{r\in S_D}|\alpha_r|^2)^{1/2}$, the triangle inequality in $L^2$ gives $\|h_D\|_4^2\le\sum_{r\in S_D}\|\alpha_r\|_4^2\le C D^{-3}$. By Parseval each shell contributes at most $e^{-ct/D^2}h_D$ to $\|u(t)\|_N$. Therefore the seed-dependent quantity

$$
V=\sum_D (D^2/c)\,h_D
 \quad\text{satisfies}\quad
 \int_0^H\|u(t)\|_N\,dt\le V,\qquad
 \|V\|_4\le C\sum_D \sqrt D\le C_V\sqrt N .
$$

The last sum runs over powers of two through $D\le N+1$. Neither the shell estimate nor the sum requires independent Fourier coefficients. [Shell size](../formal/CircleSpectralPathLength.lean#L374) · [Shell eigenvalue](../formal/CircleSpectralPathLength.lean#L411) · [Fourth norm and integrated bound](../formal/CircleSpectralPathLength.lean#L530)

### Uniform control of the nonlinear trajectory

Let $q_t$ be the row sending the grid residual to $-\dot Y(t)$ for $Y(t)=Qf_{\theta(t)}$. It uses the positive angular gate and the same admissible grid gates as $A_t$ almost everywhere. The initial kernel uses the positive gate. Integrating the one-unit half-wave gives $Y(t)=(\pi\sqrt m)^{-1}\sum_j a_j(t)\|w_j(t)\|$. The derivative of $\|w_j(t)\|$ exists almost everywhere and is zero almost everywhere on its zero set. Integrating the directional derivative at nonzero $w_j$ gives the same row as differentiating this finite sum. Write $q$ for its deterministic tangent-kernel counterpart. Define $\varepsilon_{K}$ as the sum of the RMS errors of the initial, unnormalized Gram entries against their deterministic values and of the initial angular-row entries against theirs. Cauchy–Schwarz implies $\|A_0-K\|,\|q_0-q\|\le \varepsilon_{K}$ in normalized grid coordinates. Each initial entry is an average of $m$ Gaussian marks bounded by $3\|\theta_j\|^2$ in absolute value. Centering that average gives fourth norm at most $C/\sqrt m$. Taking the RMS of the entries preserves this order by the same $L^2$ triangle inequality used for $h_D$. Thus $\|\varepsilon_{K}\|_4\le C_K/\sqrt m$. [Angular integral](../formal/CircleAngularGeometry.lean#L54) · [Joint grid and mean derivatives](../formal/CircleMeanDynamics.lean#L178) · [Initial operator errors](../formal/CircleSharpInitialization.lean#L293)

For $L_j=\|\theta_j(0)\|$, changes of the gate at $x$ inside a displacement ball of radius $\rho L_j$ require $|w_j(0)^\top x|\le\rho L_j$. Weight these indicators by $L_j^2$ and average over units. For one unit and a fixed direction, the Gaussian direction in three dimensions has absolute projection uniform on $[0,1]$, independently of its radial part. With $M=L_j^2\mathbf1_{\{|w_j(0)^\top x|\le\rho L_j\}}$ this gives $\mathbb{E} e^{M/8}=1+\rho(\mathbb{E} e^{L_j^2/8}-1)\le e^\rho$. Jensen supplies the same upper bound for the angular average of the mark. Independence and exponential Markov give probability at most $e^{-m\rho}$ that the empirical mark reaches $16\rho$. Apply this bound at the $N$ grid points and to the angular average, on a mesh of $N^{16}$ equally spaced positive radii through one. Monotonicity and rounding a radius up by at most a factor of two yield simultaneous mass bounds $32\rho$ for all $N^{-16}\le\rho\le1$. This includes radii subsequently chosen from the seed. [Marked Gaussian integral](../formal/CircleUniformMargins.lean#L56) · [Simultaneous empirical bounds](../formal/CircleUniformMargins.lean#L193)

Fix $k$ with $k+17\le N$. At width $N^{32}$ the mesh failure costs at most $2N^{-k}$. Initial concentration of the normalized tangent entries and energy costs at most $10N^{-k}$. The entry exponent at tolerance $N^{-7}$ is $mN^{-14}/36864=N^{18}/36864$, which absorbs the $O(N^2)$ tests. Another $2N^{-k}$ controls the initial output on the grid, giving $\|r(0)\|_N\le 2+64\sqrt{(k+1)\log N}\le N^2$. Thus on one Borel event of failure at most $14N^{-k}$ we have all the margin bounds, $m^{-1}\sum_j L_j^2\le4$, $\varepsilon_{K}\le4N^{-7}$, and every $L_j>0$. Within the displacement balls the two rectified feature factors are Lipschitz. For the hidden-layer product, a changed gate costs at most a margin indicator at either endpoint. The absolute one-unit entry change is at most $2L_j^2(4\rho+2\rho^2+\mathbf1_x+\mathbf1_y)$. Averaging over the units and, for $q_t$, over one angular argument gives the common bound $e=\varepsilon_{K}+234\rho$ on $\|A_t-K\|$ and $\|q_t-q\|$ for every admissible gate choice in these balls. [Initialization event](../formal/CircleSharpEvent.lean#L81) · [One-unit product estimate](../formal/CircleTangentDrift.lean#L187) · [Moving operators](../formal/CircleSharpTracking.lean#L140)

To show that the paths remain there, set $U=\min(V,N^2/\lambda)$, $\rho=32(1+U)/N^{16}$. Both entries in the minimum dominate the frozen residual integral. At $N\ge32$, the bound $\varepsilon_{K}\le\lambda/4$ and $U\le\pi^2N^4$ give $\rho\in[N^{-16},1]$, $2e\le\lambda$, and $8U/N^{16}<\rho/2$. On any prefix in the balls, subtract the frozen equation from the true one. With $w=r-u$ this gives $\dot w=-Kw+(K-A_t)r$ and $w(0)=0$. Taking the inner product with $w/\|w\|_N$ and integrating gives

$$
\|w(t)\|_N+\lambda\int_0^t\|w(s)\|_N\,ds
       \le e\int_0^t\|r(s)\|_N\,ds .
$$

The derivative of the scalar norm is zero almost everywhere where $w=0$. Since $r=u+w$, this yields $(1-e/\lambda)\int_0^t\|r\|_N\le U$. The budget $e\le\lambda/2$ gives $\int_0^t\|r\|_N\le2U$. Each parameter coordinate of neuron $j$ has speed at most $2\|\theta_j(t)\|\|r(t)\|_N/\sqrt m$, and $\|\theta_j(t)\|\le2L_j$ on the prefix. Its accumulated displacement is therefore at most $8UL_j/N^{16}<\rho L_j/2$. A first coordinate reaching that threshold contradicts the estimate, since before it the three-coordinate Euclidean displacement is at most $\sqrt3\,\rho L_j/2<\rho L_j$. This proves confinement and the integral bound through $H$ across all continuous-time gate changes. [Integrated response](../formal/CircleSharpTracking.lean#L60) · [Radius budget](../formal/CircleSharpTracking.lean#L359) · [First-exit argument](../formal/CircleSharpTracking.lean#L201)

### Projection, fitting and exceptional seeds

> **Proposition 7.2 (Long-horizon tracking and joint fitting).** Let $N\ge36865$ be odd and $m=N^{32}$. For each $\tau\in[1/2,2]$ and each valid flow selection with measurable endpoints, $\|Y_\tau-Z_\tau\|_{L^2}\le C_{\mathrm{tr}}N^{-15}$ under the full Gaussian initialization law. With probability at least $1-44N^{-158}$ the three rates $1/2,1,2$ fit at $H$ simultaneously. For the selected pair at $1/2,2$, there is a single event of probability at least $1-96N^{-158}$ on which both fit and each satisfies $|Y_\tau-Z_\tau|\le C(1+\log N)N^{-15}$. Both constants are absolute.

**Proof idea.** The constant Fourier mode of the grid kernel determines how a change in the grid residual changes the population mean. Subtracting this mode from the nonlinear evolution leaves an error controlled by the integrated residual estimate above. On exceptional seeds, loss dissipation supplies a fourth moment for the endpoint, so their contribution to the second moment remains small.

**Proof.** Define $p(v)=b_{\tau,N}Q_Nv$. The constant grid mode gives $q=pK$ and $\|p\|\le1$. Subtract the derivative of $p(r)$ from the derivative of $Y$. Since $\|q_t-pA_t\|\le2e$, the integral of this derivative difference has magnitude at most $4eU$. Also $\|r(H)-u(H)\|_N\le2eU$ by the preceding integrated inequality. Now $Y(0)-p(r(0))=Z_\tau$. The constant mode of $u(H)$ decays at rate at least $1/\pi^2$, hence $|p(u(H))|\le N^2e^{-H/\pi^2}\le N^{-16}$. We obtain the pointwise bound on the event just constructed,

$$
|Y_\tau-Z_\tau|
 \le 6\varepsilon_{K}V+\frac{44928}{N^{16}}(1+V)V+\frac{1}{N^{16}},
 \qquad 44928=6\cdot234\cdot32.
$$

[Population-row factorization](../formal/CircleGridSpectrum.lean#L550) · [Projected tracking inequality](../formal/CircleSharpTracking.lean#L266) · [Endpoint estimate](../formal/CircleSharpTracking.lean#L621)

For simultaneous fitting one may use the deterministic radius $\rho_0=32\pi^2/N^{12}$. Initial entry tolerance $N^{-7}$ and margin control leave a lower bound $\kappa=3/(4\pi^2N^2)$ on the true Gram in this radius. Starting at RMS at most $N^2$, coercivity gives $\|r(t)\|_N\le N^2 e^{-\kappa t}$ on each confined prefix. Its integral is at most $N^2/\kappa$, and $4N^2/(N^{16}\kappa)<\rho_0/2$ closes the coordinate argument. Since $\kappa H\ge5\log N$, all three rates fit. A single initial event costs $14N^{-k}$ and the three rate-specific tests cost $10N^{-k}$ apiece. For the sharper angular statement at the two compared rates, the Gaussian entry and Fourier-coefficient tails also imply $\varepsilon_{K}\le C_k\sqrt{\log N}/N^{16}$ and $V\le C_k(1+\sqrt{\log N})\sqrt N$ on a common event of failure at most $52N^{-k}$. For example, a modewise threshold proportional to $(1+u_{\rm tail})/D^2$ costs at most $4N\exp(-u_{\rm tail}^2/4096)$ over all residues for $0\le u_{\rm tail}\le128\sqrt m$. The choice $u_{\rm tail}=64\sqrt{(k+1)\log N}$ lies in this range at the stated width. Substitution above and intersection with the fitting event yield simultaneous fit and $|Y_\tau-Z_\tau|\le C_k(1+\log N)/N^{15}$ at both rates with failure at most $96N^{-k}$. In particular take $k=158$. [Fitting constants](../formal/CircleActualTracking.lean#L310) · [Joint event](../formal/CircleSharpTracking.lean#L642) · [Mode tails](../formal/CirclePairedOrdering.lean#L310) · [Paired angular event](../formal/CirclePairedOrdering.lean#L388) · [Logarithmic factor](../formal/CirclePairedOrdering.lean#L658)

Finally take $k=68$ in the per-rate projected bound and write $D_H=Y_\tau-Z_\tau$. Hölder on its good event gives

$$
\|\mathbf1_G D_H\|_2\le 6\|\varepsilon_{K}\|_4\|V\|_4+
    44928N^{-16}(\|V\|_4+\|V\|_4^2)+N^{-16}\le C N^{-15}.
$$

This application of Hölder allows dependence between the initial operator and the residual. On every trajectory, expand $a_j(H)\|w_j(H)\|-a_j(0)\|w_j(0)\|$, use the reverse triangle inequality on the hidden norm, and sum with Cauchy–Schwarz. With the displacement estimate this bounds $|Y(H)-Y(0)|$ by

$$
\sqrt{2H}\,(\|\theta(0)\|^2/m+L(0))+(2H/\sqrt m)L(0).
$$

The initial energy per neuron and the initial loss have bounded fourth norms uniformly in $N,m$. For the loss this follows from bounded eighth moments of the initial network output at each unit input and the triangle inequality for the grid average of squared residuals. Also $|Y(0)-Z_\tau|\le\|r(0)\|_N$. Thus $\|D_H\|_4\le C(1+\sqrt H+H/\sqrt m)$, bounded by $C N^{3/2}$ already using the bound $H=O(N^3)$. Hölder on the complement gives $\|\mathbf1_{G^c}D_H\|_2\le C N^{3/2}(14N^{-68})^{1/4}=O(N^{-31/2})$. Adding the two contributions proves the claimed $O(N^{-15})$ over the full Gaussian seed law. [Pathwise displacement envelope](../formal/CircleFlowMoments.lean#L270) · [Fourth norm](../formal/CircleFlowMoments.lean#L407) · [Exceptional-set split and final estimate](../formal/CircleSharpMoments.lean#L81)

$\square$

**Lean proof.** The unconditional bound is [sharp_tracking](../formal/CircleSharpMoments.lean#L159). The three-rate event is [joint_fit_original_horizon](../formal/CircleSharpTracking.lean#L642). The per-rate bound on the paired event follows from [paired_likely_cap](../formal/CirclePairedOrdering.lean#L388) and [endpointCap_le](../formal/CirclePairedOrdering.lean#L658) by intersecting with the fitting event, as in [common_event](../formal/CirclePairedTheorem.lean#L41).

## Ordering and statistical bias under gradient flow

Write $e_\tau=Y_\tau-Z_\tau$ for the two endpoint errors. Canceling the shared initial mean gives

$$
N^2\Delta-c_NX=N^2(e_{1/2}-e_2),\qquad
\|N^2\Delta-c_NX\|_2\le 2C_{\mathrm{tr}}N^{-13}.
$$

The norm is over the Gaussian seed. The second assertion uses the per-rate $L^2$ tracking bound $C_{\mathrm{tr}}N^{-15}$. Both assertions apply to every measurable choice of the two admissible flows on sufficiently large odd grids. [Reference mean](../formal/CircleEscapeBridge.lean#L145) · [Paired identity](../formal/CirclePairedOrdering.lean#L57) · [All-seed bound](../formal/CirclePairedOrdering.lean#L352)

### Ordering across all seeds

> **Proposition 8.1 (Ordering from the initial deficit).** There is an absolute $C$ such that, for every sufficiently large odd $N$, every measurable pair of the two flows at width $N^{32}$ satisfies $\Pr(\Delta X\le0)\le C N^{-13}$ at time $H$. Ties are included.

**Proof idea.** A wrong ordering requires the deficit to be smaller than the error in the paired prediction. The error and the deficit depend on the same Gaussian weights. Mixing three independent readouts along a random direction makes the initial grid mean linear in that direction and gives a radius for the error that is independent of the direction. Spherical area then bounds the probability of a miss.

**Proof.** Write the miss event as $M=\{\Delta X\le 0\}$. On $M$, the distance from $N^2\Delta$ to $c_NX$ is at least $c_N|X|$. A first estimate conditions on the hidden weights. Given them, $Q_Nf_0$ is centered Gaussian with variance $v$. For $x\ge 1/2$ and $v>0$, putting $s=x/\sqrt v$ bounds its density by

$$
\frac{s e^{-s^2/2}}{x\sqrt{2\pi}}\le \frac{2e^{-1/2}}{\sqrt{2\pi}}.
$$

Integrating over $[1-\delta,1+\delta]$ gives $\Pr(|X|\le\delta)\le 4\delta e^{-1/2}/\sqrt{2\pi}$ for $0\le\delta\le 1/2$, since the point mass at zero when $v=0$ lies outside this interval. Using the common-event tracking bound as a deterministic radius gives $O(N^{-13}(1+\log N))$. Removing the logarithm requires a bound that respects the dependence of $X$ and both tracking errors on the same readouts. [Miss inequality](../formal/CirclePairedOrdering.lean#L64) · [Gaussian band integration](../formal/CircleScoreMargin.lean#L54) · [Common tracking event](../formal/CirclePairedTheorem.lean#L41)

Draw a hidden layer and three independent standard Gaussian readouts $a^{(1)},a^{(2)},a^{(3)}$. Denote these four draws by $p$. Independently draw a uniform direction $u$ on the two-dimensional unit sphere in $\mathbb{R}^3$, and use the readout $a(u)=\sum_i u_i a^{(i)}$. Every fixed $u$ has the prescribed seed law, since its coordinates form a unit vector and each neuron uses independent Gaussian draws. With $p$ fixed, linearity gives $Q_N f_0(u)=A(p)\cdot u$, where $A_i(p)$ is the grid mean using $a^{(i)}$. This supplies a random direction over which one can integrate the miss event. [Gaussian law and Fubini](../formal/CircleReadoutMixing.lean#L70) · [Linearity of the grid mean](../formal/CircleMixingEnvelopes.lean#L231)

For this integration the radius must hold uniformly in $u$. Let $\bar{\varepsilon}_{K}(p)$ bound the sum of the initial grid-kernel and population-row errors at either rate, and let $V(p)$ bound the weighted sum of the initial residual Fourier-block norms used in the tracking estimate. To construct $\bar{\varepsilon}_{K}$, each kernel entry is a constant plus a quadratic form in $u$. Its values along the three coordinate axes and their three pairwise unit bisectors recover the cross terms by polarization. The interpolation coefficients have absolute value at most three. For $V$, residual coefficients are affine in $u$, so the six signed coordinate axes suffice, with coefficients of absolute value at most one. Taking norms and summing gives simultaneous bounds in all directions. Each of the finitely many directions has the prescribed Gaussian law. The triangle inequality in $L^4$ then gives $\|\bar{\varepsilon}_{K}\|_4\le c_K N^{-16}$ and $\|V\|_4\le c_V\sqrt N$ for absolute constants. [Finite interpolation](../formal/CircleMixingEnvelopes.lean#L29) · [Uniform bounds](../formal/CircleMixingEnvelopes.lean#L244) · [Fourth moments](../formal/CircleMixingEnvelopes.lean#L292)

The path estimate at confidence exponent 13 gives a common measurable event $G$ of failure probability at most $28N^{-13}$. Whenever the mixed seed belongs to $G$, both endpoint errors are bounded by

$$
E(p)=6\bar{\varepsilon}_{K}V+N^{-16}\bigl[44928(1+V)V+1\bigr].
$$

Cauchy–Schwarz gives $\mathbb{E}[\bar{\varepsilon}_{K}V]\le c_K c_VN^{-31/2}$ and $\mathbb{E}[V^2]\le c_V^2 N$, hence $\mathbb{E} E\le K N^{-15}$ with $K=6c_K c_V+44928(c_V+c_V^2)+1$. For a seed in $M\cap G$, the miss inequality now forces $|1-A(p)\cdot u|\le r(p)=2N^2E(p)/c_N$. Only $p$ enters this radius. [Path event](../formal/CirclePairedOrdering.lean#L473) · [Integrated tracking bound](../formal/CirclePairedOrdering.lean#L446)

For any fixed vector $A$ and radius $r\ge0$, the spherical probability of $|1-A\cdot u|\le r$ is at most $4r$. For $0<r<1/4$, the band is empty if $\|A\|<1-r$. Otherwise $|A\cdot u|/\|A\|$ is uniform on $[0,1]$ by rotation invariance and spherical area. The band is contained in an interval of this coordinate of length at most $2r/\|A\|\le4r$. For $r\ge1/4$ the probability bound follows from total mass one, and $r=0$ follows by continuity from above. For each $p$, the directions whose mixed seed lies in $M\cap G$ occupy at most this band. Integrating over $u$ and then $p$, and using the Gaussian seed law for $G^c$, gives

$$
\Pr(M)\le \Pr(G^c)+4\mathbb{E}[r(p)]
\le (28+8K/c_N)N^{-13}.
$$

Since $c_N\to\pi^2/40>0$, the constants are uniform in large odd $N$ and in the selected flows. [Spherical projection law](../formal/CircleSphereBand.lean#L80) · [Random-radius integration](../formal/CirclePairedOrdering.lean#L433) · [Ordering theorem](../formal/CirclePairedOrdering.lean#L573)

$\square$

**Lean proof.** The spherical estimate gives the finite-$N$ bound [actual_wrong_probability](../formal/CirclePairedOrdering.lean#L573) and the uniform asymptotic conclusion is [actual_wrong_eventually](../formal/CirclePairedOrdering.lean#L609).

### Conditioning on a fixed initial margin

For $\gamma>0$ write $A_\gamma=\{|X|\ge\gamma\}$, and let $p_\gamma=\Phi(-\pi\gamma)/2$, with $\Phi$ the standard normal distribution function.

> **Corollary 8.2 (Separation at fixed margin).** Fix $\gamma>0$. For every sufficiently large odd $N$ and every measurable flow pair at width $N^{32}$, conditional on $A_\gamma$, both copies fit and satisfy $\Delta X>0$ and $|\Delta|\ge c_N\gamma/(2N^2)$ with probability at least $1-96/(p_\gamma N^{158})$.

**Proof idea.** On a fixed margin the paired prediction is bounded away from zero after scaling by $N^2$. Its error tends to zero on the tracking event. Conditioning costs only a constant because the initial grid mean has a Gaussian tail of positive mass uniformly in $N$.

**Proof.** The common event $F$ for fitting and tracking has $\Pr(F^c)\le96N^{-158}$. Eventually its error bound on $N^2\Delta$ is at most $c_N\gamma/2$. On $F\cap A_\gamma$ this proves $\Delta X>0$ and $|\Delta|\ge c_N\gamma/(2N^2)$, although the networks' grid predictions differ by at most $2N^{-3}$ in grid RMS. If $\gamma\le |X|\le \Gamma$ for a fixed $\Gamma\ge\gamma$, the same event gives the two-sided estimate

$$
\frac{\pi^2\gamma}{160N^2}\le |\Delta|\le
\frac{\pi^2(\Gamma+\gamma/2)}{20N^2}.
$$

This uses the eventual bounds $\pi^2/80\le c_N\le\pi^2/20$. [Separation on the common event](../formal/CirclePairedTheorem.lean#L63) · [Fixed-band bounds](../formal/CirclePairedTheorem.lean#L185)

To normalize the conditional probability, write $g(w)=Q_N[w^\top x]_+$ for one neuron's grid feature. Given the hidden layer, the grid mean has variance $v=m^{-1}\sum_jg(w_j)^2$. The odd-grid second-moment calculation gives $\mathbb{E}[g(w)^2]\ge 2/\pi^2$, and a fourth-moment bound gives $\Pr(v<1/\pi^2)\le15\pi^4/m$. Eventually at least half the hidden layers have $v\ge1/\pi^2$. On those layers the conditional probability of $Q_Nf_0\le-\gamma$ is at least $\Phi(-\pi\gamma)$, since the conditional standard deviation is at least $1/\pi$. This event implies $A_\gamma$, so $\Pr(A_\gamma)\ge p_\gamma$. It follows that $\Pr(F\mid A_\gamma)\ge 1-96/(p_\gamma N^{158})$. [Variance lower tail](../formal/CircleFourthSmallBall.lean#L31) · [Margin probability](../formal/CircleMarginMass.lean#L66) · [Conditional success](../formal/CirclePairedTheorem.lean#L167)

$\square$

**Lean proof.** The joint margin statement is [fixed_margin_complete](../formal/CirclePairedTheorem.lean#L146), its conditional form is [conditional_success](../formal/CirclePairedTheorem.lean#L167), and the two-sided refinement is [fixed_band](../formal/CirclePairedTheorem.lean#L185).

### The limiting coefficient and the signed shift

Write $c_*=\pi^2/40$.

> **Corollary 8.3 (Expected shift and leading RMS constant).** Along every growing sequence of odd grids at width $m=N^{32}$, for any sequence of measurable flow pairs at horizon $H$,
>
> $$
> \mathbb{E}\Delta=\frac{c_N}{N^2}+O(N^{-15})
> =\frac{\pi^2}{40N^2}-\frac{\pi^4}{1600N^4}+O(N^{-6}),
> $$
>
> $$
> N^4\left\|\Delta-\frac{c_* X}{N^2}\right\|_2
> \longrightarrow \frac{\pi^4}{1600}\sqrt{1+\frac{2}{\pi^2}} .
> $$

**Proof idea.** The reference transfers a deterministic multiple of the deficit, whose expectation is one. The next term in the finite-grid coefficient gives the leading RMS error when the limiting slope replaces the exact one. Proposition 7.2 puts the nonlinear flow error below both scales.

**Proof.** Let $S_N$ denote the sum of the nonzero covariance Fourier coefficients that alias into the grid mean. The spectral calculation gives $S_N=O(N^{-4})$. For the reference $Z(b)=Qf_0+bX$ at an arbitrary interpolation weight $b$,

$$
\mathbb{E}[Z(b)^2]=(2/\pi^2)(1-b)^2+b^2 S_N+b^2.
$$

Substitution into $X^2=2Z(0)^2+2Z(1)^2-4Z(1/2)^2$ gives $\|X\|_2=\sqrt{1+2/\pi^2+S_N}$. The reverse triangle inequality bounds the difference between $\|N^2\Delta-c_*X\|_2$ and $|c_N-c_*|\,\|X\|_2$ by $2C_{\mathrm{tr}}N^{-13}$. Multiplying by $N^2$ and using $N^2(c_N-c_*)\to-\pi^4/1600$ proves the stated RMS limit. [Reference moments](../formal/CircleReferenceMoments.lean#L185) · [Deficit RMS](../formal/CirclePairedSecondOrder.lean#L21) · [Second-order limit](../formal/CirclePairedSecondOrder.lean#L93)

Finally, statistical bias at rate $\tau$ is $\mathbb{E}[Y_\tau]-1$. Conditional on the hidden layer the initial readout is centered, hence $\mathbb{E}[Q_Nf_0]=0$ and $\mathbb{E} X=1$. Taking expectations in the paired identity and applying Cauchy–Schwarz gives

$$
\left|\mathbb{E} Y_{1/2}-\mathbb{E} Y_2-\frac{c_N}{N^2}\right|
\le 2C_{\mathrm{tr}}N^{-15}.
$$

Dividing the remainder bound of Corollary 2.3 by $N^2$ shows that the error after both displayed terms of the signed expansion is at most $2C_{\mathrm{tr}}N^{-15}+400N^{-6}$. In particular, slowing the hidden layer increases the expected population mean for sufficiently large odd $N$. [Reference expectations](../formal/CircleReferenceMoments.lean#L200) · [All-seed tracking](../formal/CirclePairedTheorem.lean#L209)

$\square$

**Lean proof.** [signed_mean_finite](../formal/CirclePairedTheorem.lean#L234) proves the finite-grid mean bound and [signed_mean_expansion](../formal/CirclePairedTheorem.lean#L264) gives its two-term expansion. [leading_rms](../formal/CirclePairedSecondOrder.lean#L93) proves the limit. The signed estimate applies [mean_transfer](../formal/CircleComparison.lean#L116) at the two rates, with [sharp_tracking](../formal/CircleSharpMoments.lean#L159) and [weighted_reference_moments](../formal/CircleReferenceMoments.lean#L200). The expansion is [uniform_remainder](../formal/CircleCoefficientRemainder.lean#L91).

## Discussion

The coefficient $\pi^2/40$ arises because frequencies that agree with a constant on the sampled grid can have zero average around the circle. Changing the relative hidden rate changes the weight of these frequencies in the tangent kernel. The two runs therefore transfer different fractions of the initial grid deficit to their population means. The nonlinear estimates bound the error in this calculation for the trained networks themselves.

The leading off-grid effect itself is small. For unit deficit the finite-grid reference gap is about $0.0266$ at $N=3$ and $0.000257$ at $N=31$. The nonlinear results concern the population mean of a two-layer, full-batch network in the kernel regime, with a particular grid and teacher. A first-harmonic calculation gives a second kernel observable. Extending the trajectory estimates to other observables or to stochastic training would require additional control.

## Use of AI tools and author contributions {.unnumbered}

The author selected the research question and directed the investigation. OpenAI Codex and Anthropic Claude developed proofs and Lean formalizations, implemented and analyzed numerical experiments, and drafted manuscript text under that direction. The author has read the manuscript, including all theorems and experiments, and takes responsibility for its contents. The mathematical results are formalized in Lean and checked against the definitions identified in the statement audit. Experimental interpretations depend on the simulation and statistical analysis described in the paper.

## Formalization and reproducibility

In Lean the positive grid size is written `n+1`. The declaration `CirclePairedGDTheorem.paired_discrete_gradient_descent` combines the high-probability fitting event, the sign bound, convergence in probability, and divergence of both unscaled mean-square predictions for the actual discrete updates. For flow, `CirclePairedTheorem.common_event` and `CirclePairedTheorem.all_seed_bounds` give the shared fitting estimate and unconditional bounds. The expected shift is `CirclePairedTheorem.signed_mean_expansion`. The leading RMS constant is `CirclePairedSecondOrder.leading_rms`. The probability theorems start from the Gaussian initialization law. The separate numerical certificates use the recorded pairs as inputs. [Discrete statement](../formal/CirclePairedGDTheorem.lean#L59) · [Flow statement](../formal/CirclePairedTheorem.lean#L209) · [Proof guide](../docs/proof-guide.md)

Appendix B prints the complete Lean declarations for the paired training laws, the signed flow bias expansion, and two steps inside the proofs. The typesetter checks each listing against the cited source lines. The PDF also embeds `proof-sources.zip`, containing the full Lean development, pinned build inputs, numerical proof input and verification record. The source links following each mathematical proof identify the declarations that justify its steps, down to index conversions and routine norm estimates. [Selected Lean proofs](#appendix-selected-lean-proofs)

To replay the formalization, extract the attached archive or use a repository checkout. With Git, elan and Python 3.11 or newer, run the following from its root.

```sh
cd formal
lake exe cache get
python3 verify.py --report .lake/replay
```

The development uses Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679` [@demoura2021; @mathlib2020]. The paper’s import closure contains 145 project library modules and 5,428 safe declarations, including 4,511 theorems. The paper audit prints the axioms of the 209 theorem declarations cited directly. The verification record identifies the closed export replayed through Lean’s kernel checker in standard and paranoid modes. Its foundational axioms are propositional extensionality, classical choice and quotient soundness. The receipt records source and data hashes, dependency revisions and the SHA-256 fingerprint of the exported proof objects. [Receipt](../formal/verification/receipt.json) · [Standard replay](../formal/verification/kernel.log) · [Paranoid replay](../formal/verification/paranoid.log)

::: {.named-only}
The code, data and verification record for this edition are archived under tag `paper-v3`.
:::

## Appendix. Equal layer rates, step selection and unconditional moments

### The reference and its moments

> **Definition A.1 (Equal-rate benchmark).** Both layers have multiplier one. On the odd circle grid with the teacher and Gaussian initialization of Section 1, write $P=Qf_0$, $G=Q_Nf_0$ and $Y_T=Qf_T$. The equal-rate kernel reference is $Z=P+b(1-G)$ with $b=b_{1,N}$. Unless another width or time is specified, take $m=N^{32}$ and the common deterministic endpoint $H$. A fit at $T$ means $\|f_T-y\|_N\le N^{-3}$.

The readouts of independent replicas are drawn afresh along with their hidden weights. For $r\ge1$ such replicas write $\bar Y_T=r^{-1}\sum_{i=1}^r Y_T^{(i)}$. [Reference in Lean](../formal/CircleEscapeBridge.lean#L145)

> **Corollary A.2 (Bias, variance and ensembles under gradient flow).** Along odd $N\to\infty$, for every measurable selection of equal-rate flows, $\|Y_H-Z\|_{L^2}=o(N^{-2})$ and
>
> $$
> N^2(\mathbb{E} Y_H-1)\longrightarrow-\pi^2/36,\qquad
> N^4\mathrm{Var}(Y_H)\longrightarrow7\pi^2/1620 .
> $$
>
> For fixed $r\ge1$ independent seeds trained with the same selection, $N^4\mathbb{E}[(\bar Y_H-1)^2]\to\pi^4/1296+7\pi^2/(1620r)$.

**Proof idea.** Only integer multiples of the grid size can contribute to the difference between the two initial means. Their covariance gives the variance constant for $Z$. Root-mean-square tracking transfers it to the trained network.

**Proof.** The readouts are centered and independent of the initial hidden weights, so $\mathbb{E}P=\mathbb{E}G=0$. Write $h_k$ for the Fourier coefficients of $[\cos u]_+$. Averaging a neuron's uniform orientation pairs each mode with its conjugate, and its squared radius has expectation two. Independence of the neurons and the $m^{-1/2}$ normalization give the initial covariance coefficients $2|h_k|^2$. The population average retains frequency zero. Grid averaging retains all multiples of $N$, of which only the even multiples can contribute at nonzero frequency for odd $N\ge3$. Hence

$$
v_0=\mathrm{Var}(P)=\mathrm{Cov}(P,G)=2/\pi^2,\qquad
S_N=\mathrm{Var}(G)-v_0=\frac{4}{\pi^2}\sum_{j\ge1}\frac{1}{((2Nj)^2-1)^2}.
$$

In particular $P$ and $G-P$ are uncorrelated. Since $Z-b=(1-b)P-b(G-P)$, we have $\mathbb{E} Z=b$ and $\mathrm{Var}(Z)=(1-b)^2v_0+b^2S_N$.

The equal-rate kernel gives $b=(1+A+B/3)^{-1}$ with the alias sums from the coefficient calculation, $A=O(N^{-4})$ and $N^2B\to\pi^2/12$. Thus $N^2(1-b)\to\pi^2/36$. In $N^4S_N$ the summands are dominated by a constant times $j^{-4}$. Since $\sum_{j\ge1}j^{-4}=\pi^4/90$, dominated convergence gives $N^4S_N\to\pi^2/360$. The limiting scaled variance is therefore $(\pi^2/36)^2(2/\pi^2)+\pi^2/360=7\pi^2/1620$.

Equal-rate nonlinear tracking gives $\|Y_H-Z\|_{L^2}=o(N^{-2})$. Each difference in means and in standard deviations is bounded by this norm. For the latter, apply the reverse triangle inequality to the centered variables and use $\mathrm{Var}(Y_H-Z)\le\mathbb{E}[(Y_H-Z)^2]$. This proves both trained limits. Finally independence eliminates off-diagonal centered products, yielding $\mathbb{E}[(\bar Y_H-1)^2]=(\mathbb{E}Y_H-1)^2+\mathrm{Var}(Y_H)/r$. The squared bias accounts for about $63.8\%$ of the single-run limit.

$\square$

**Lean proof.** [`circle_reference_variance`](../formal/CircleStats.lean#L224) · [`S_eq_alias_sum`](../formal/CircleSpectrum.lean#L277) · [`scaledS_limit`](../formal/CircleSpectrum.lean#L154) · [`sd_transfer`](../formal/CircleStats.lean#L113) · [`equal_rate_tracking_littleO`](../formal/CircleComparison.lean#L264) · [`equal_rate_limits`](../formal/CircleComparison.lean#L251) · [`ensemble_limit`](../formal/CircleComparison.lean#L304)

### An initialization-dependent step size

> **Definition A.3 (Capped step and training clock).** Let $J_s$ be the prediction Jacobian on the grid, using ReLU slope zero at equality, and let $\Lambda_s=\lambda_{\max}(J_sJ_s^\top/N)$. Capped GD measures $\Lambda_0$ once and takes every update with $\eta_*=1/\max(1,\Lambda_0)$. Its endpoint is update $H$, with elapsed time $H\eta_*$. On the acceptance event $E=\{\Lambda_0\le1\}$ its entire trajectory coincides with unit-step GD.

The inclusion of $1/N$ in $\Lambda_s$ comes from averaging the training loss on the grid. [Capped rate in Lean](../formal/CircleInitializationCheck.lean#L17) · [Acceptance event](../formal/CircleCapMoments.lean#L435)

> **Lemma A.4 (Energy and curvature along capped GD).** Let $N\ge81$ be odd, $m\ge1$, and $T$ a nonnegative integer with $200T\le m$. For almost every Gaussian initialization, writing $P_s=\|\theta_s\|^2/m$, for every $s\le T$ one has $P_s\le P_0+12\eta_*s/m$ and $\eta_*\Lambda_s\le7/2$. In particular $\|Y_T\|_{L^4}=O(\sqrt m)$, with an absolute implied constant.

**Proof idea.** Circle geometry compares initial curvature with initial energy. The positive margin $4-7/2$ in the discrete energy increment then bounds the accumulation of energy throughout training.

**Proof.** Put $u_N=1/4+4/N$ and $\ell_N=(1/\pi-2/N)^2$. For any unit vector $v$, the whole-circle average of $(v^\top x)^2$ restricted by a semicircle gate is $1/4$. Comparing its grid sum with the integral gives the uniform upper bound $u_N$. Apply it to the squared readout features and the projections of the hidden-coordinate Jacobian to get $\Lambda_s\le u_NP_s$. For the reverse inequality at initialization, test the constant grid vector. A unit's mean activation is at least $(1/\pi-2/N)\|w_j\|$. Projecting the mean gated input onto $w_j/\|w_j\|$ gives a lower bound $1/\pi-2/N$. Squaring, weighting and summing the readout and hidden contributions gives $\ell_NP_0\le\Lambda_0$ almost surely. The Gaussian hidden vectors are nonzero almost surely.

Suppose $P_s\le P_0+12\eta_*s/m$. Since $\eta_*\Lambda_0\le1$, the geometric bounds give $\eta_*\Lambda_s\le u_N/\ell_N+12u_N\eta_*^2s/m\le7/2$ on the stated time interval. Let $r=f_s-y$, $R_s=\|r\|_N$ and $\langle\cdot,\cdot\rangle_N$ denote the grid inner product. Expand the squared norm after the simultaneous update, use $J_s\theta_s=2f_s$, and complete the square to obtain

$$
m(P_{s+1}-P_s)
\le\eta_*\big[(\eta_*\Lambda_s-4)R_s^2-4\langle y,r\rangle_N\big]
\le8\eta_*\|y\|_N^2=12\eta_* .
$$

The last equality uses the teacher’s grid mean square $3/2$. This closes the induction. For the benchmark, $200H\le m$. Finally $|Y_T|\le\sqrt m P_T/(2\pi)$ by $2|a_j|\|w_j\|\le a_j^2+\|w_j\|^2$, and the fourth moment of the average initial energy is bounded by a single neuron's eighth Gaussian moment.

$\square$

**Lean proof.** [`grid_mean_lower`](../formal/CircleAngularGeometry.lean#L103) · [`gram_upper`](../formal/CircleCapInduction.lean#L224) · [`gram_lower`](../formal/CircleCapInduction.lean#L269) · [`actual_increment`](../formal/CircleCapInduction.lean#L75) · [`circle_cap_81`](../formal/CircleCapInduction.lean#L388) · [`cap_through_fitHorizon`](../formal/CircleCapInduction.lean#L433) · [`capped_fourth`](../formal/CircleCapMoments.lean#L264)

> **Proposition A.5 (Capped GD and conditioning on acceptance).** At the benchmark width and endpoint, capped GD fits with probability $1-O(N^{-158})$ and satisfies $\|Y_H-Z\|_{L^2}=O(N^{-15})$ over all seeds. Unit-step GD satisfies the same estimates conditional on $E$. Both laws give the bias, variance and independent-ensemble limits of Corollary A.2. For odd $N\ge81$ and any $m\ge1$, $e^{-20m}\le\Pr(E^c)\le e^{-m/240}$.

**Proof idea.** Compare each GD segment with the frozen-kernel update. Gaussian concentration controls the gates through all $H$ steps on typical seeds, and Lemma A.4 controls the contribution of the exceptional seeds to the second moment.

**Proof.** For the upper rejection bound, use $\Lambda_0\le u_NP_0$ and the Gaussian exponential moment $\mathbb{E}\exp(g^2/32)=\sqrt{16/15}$ in the $3m$ independent coordinates. For the lower bound restrict every coordinate to $[2,3]$. This event has probability at least $e^{-20m}$ and gives $P_0\ge12$, hence $\ell_NP_0>1$.

Write $l_j=\|(a_{j,0},w_{j,0})\|$. If the displacement of neuron $j$ stays below $\rho l_j$, its preactivation on a unit input moves by at most $\rho l_j$. A gate can change only when $|w_{j,0}^\top x|\le\rho l_j$. Weight the corresponding indicator by $l_j^2$ and average over neurons to obtain $M_\rho(x)$. For $0\le\rho\le1$, the normalized projection of a three-dimensional Gaussian direction is uniform on $[-1,1]$ and independent of the squared radius. Thus $\mathbb{E}M_\rho(x)=3\rho$. The change in a mixed Jacobian product entry at $x,y$ between two states within this displacement bound is at most

$$
(4\rho+2\rho^2)P_0+M_\rho(x)+M_\rho(y).
$$

Integrating this estimate along each straight GD segment accounts for its gate crossings.

For unit-step GD on the concentration event, let $U$ bound the sum of the frozen-kernel RMS residuals through the endpoint and $\varepsilon_{K}$ bound the initial discrepancies in the grid kernel and population row. Concentration bounds the marked masses entering the preceding display. If $2(\varepsilon_{K}+234\rho)\le(\pi N)^{-2}$, the perturbed residual recurrence has cumulative RMS at most $2U$. Its displacement stays within the assumed allowance when $16U/\sqrt m\le\rho$, closing the induction. Subtraction of the stopped kernel prediction cancels the constant mode, leaving a population-mean error at most $6(\varepsilon_{K}+234\rho)U$. At $H$, the Fourier residual bounds give an $O(N^{-15})$ contribution to RMS. The exceptional set, including rejection by the curvature cap, has probability $O(N^{-158})$. On that set Hölder and Lemma A.4 bound the RMS contribution by $O(N^{16}(N^{-158})^{1/4})=O(N^{-47/2})$.

Thus capped GD inherits the fitting probability and the all-seed estimate. On $E$ its iterates equal the unit-step iterates. Restrict the squared-error integral to $E$ and divide by $\Pr(E)$ to obtain the conditional bound. The exponentially small rejection probability perturbs the reference moments negligibly by Hölder. The moment-transfer argument of Corollary A.2 finishes the proof.

$\square$

**Lean proof.** [`reject_probability`](../formal/CircleCapMoments.lean#L295) · [`reject_lower`](../formal/CircleCapMoments.lean#L528) · [`entry_drift`](../formal/CircleTangentDrift.lean#L205) · [`marked_energy`](../formal/CircleInitializationConcentration.lean#L730) · [`sharp_stop`](../formal/CircleSharpGD.lean#L84) · [`gaussian_horizon_fit`](../formal/CircleDiscreteMoments.lean#L95) · [`capped_horizon_sharp`](../formal/CircleSharpGDMoments.lean#L248) · [`accepted_benchmarks_sharp`](../formal/CircleSharpGDMoments.lean#L357) · [`capped_benchmark_limits`](../formal/CircleGDLimits.lean#L174) · [`accepted_benchmark_limits`](../formal/CircleGDLimits.lean#L367)

### Fixed-step gradient descent at three horizons

> **Lemma A.6 (Opposite Gaussian tails).** For $N\ge3$, $m\ge1$, any fixed step $0<\eta\le1$ and any integer $T\ge0$, set $L^2=64m/\eta$ with $L>0$. The equal-rate GD mean has finite variance and
>
> $$
> \mathrm{Var}(Y_T)\ge e^{-896m^2/\eta} A_T^2,\qquad
> A_T=\frac{\sqrt m}{\pi}\bigl(L2^{3^T}\bigr)^2 .
> $$
>
> Each of two seed sets of probability at least $e^{-896m^2/\eta}$ produces one sign of the deviation from zero, at magnitude at least $A_T$. Both sets miss the benchmark tolerance at every iterate.

**Proof idea.** On each seed box all readouts have the same sign. One GD step flips every readout and sends both layer magnitudes above a common cubic lower bound. The two boxes give opposite terminal signs.

**Proof.** In both boxes each hidden coordinate lies in $[2L,3L]$. Put all readouts in $[2L,3L]$ in one box and $[-3L,-2L]$ in the other. Bounding the Gaussian density below on each interval and multiplying probabilities gives the stated mass. Let $\sigma$ be the current common readout sign. Suppose every signed readout $A=\sigma a_j$ and hidden radius $W=\|w_j\|$ is at least $s\ge2L$. With $h_i=[w_j^\top x_i]_+$, the projections have mean zero, RMS $W/\sqrt2$ and magnitude at most $W$. Hence $Q_Nh=Q_N|w_j^\top x|/2\ge W/4$ and $Q_Nh^2\ge W^2/16$. All signed network contributions are nonnegative. Keeping just unit $j$ and using $|y_i|\le2$ gives

$$
D=\frac{\eta}{\sqrt m} Q_N[\sigma(f-y)h]
\ge\frac{\eta}{\sqrt m}\left(\frac{AW^2}{16\sqrt m}-2W\right)
\ge\frac{2AW^2}{L^2},
$$

where $AW/\sqrt m\ge64$. The readout in the opposite sign is now $D-A$. The identity $\mathbf1_{\{w_j^\top x_i>0\}}(w_j^\top x_i)=h_i$ gives $-w_j^\top w'_j=AD-W^2$, so $\|w'_j\|\ge(AD-W^2)/W$. Both updated magnitudes are at least $s^3/L^2$. From $s_0=2L$ we thus obtain $s_T=L2^{3^T}$. The signed population mean is at least $\sqrt m\,s_T^2/\pi$, and the signed grid mean is at least $\sqrt m\,s_T^2/4$. Since the grid target has mean one, the latter bound rules out a fit for either sign.

At least one box lies at distance $A_T$ or more from the unconditional mean, giving the variance inequality. Each finite iterate has finite second moment by the Gaussian polynomial envelope.

$\square$

**Lean proof.** [`grid_relu_sum_bounds`](../formal/CircleGridMargin.lean#L49) · [`step_cone_grid`](../formal/CircleGridEscape.lean#L60) · [`circle_escape_uniform`](../formal/CircleGridEscape.lean#L136) · [`benchmark_bounds_uniform`](../formal/CircleGridEscape.lean#L183) · [`trained_memLp`](../formal/CircleSeedIntegrability.lean#L226) · [`signed_boxes_never_hit`](../formal/CircleConditioning.lean#L300)

> **Corollary A.7 (Three endpoints of one unit-step trajectory).** Set $S=\lceil\pi^2\log N\rceil$ and $M=\lceil60\log N\rceil$. Along odd $N\to\infty$ at $m=N^{32}$, unit-step GD has the bias, variance and ensemble limits of Corollary A.2 at $S$. The probability of any fit through $M$ is $O(1/N)$. At each of $M$ and $H$ both $\mathrm{Var}(Y_T)$ and $\mathbb{E}[(Y_T-Z)^2]$ diverge. At $H$ the fit probability tends to one.

**Proof idea.** Gaussian tails still control the high moments needed to track $Z$ at $S$. By $M$, the cubic growth from Lemma A.6 dominates the probability cost of the escaping seeds.

**Proof.** At $S$ the stopped reference replaces $b$ by $b[1-(1-\gamma)^S]$, where $\gamma\in[3/\pi^2,1]$ is the constant-mode eigenvalue of the normalized kernel. Thus the coefficient discrepancy is at most $N^{-3}$. The mean-square error to the stopped reference is $O(N^{-10})$. On the concentration event this follows by summing the mixed-kernel errors. On its complement, a polynomial envelope grows at most cubically per update. Through $S$ the degree needed for the fourth moment is at most $24N^{24}$. Gaussian moments and the exponentially small rejection probability at width $N^{32}$ absorb this growth. Since $1-G$ has bounded second moment, $\|Y_S-Z\|_{L^2}=o(N^{-2})$. The transfer calculation of Corollary A.2 applies.

Through $M$ the frozen dynamics retain at least $1/N$ of the initial fourth Fourier coefficient of the residual. A fit on the tracking event would force the real part of that initial coefficient into $[-1/N,1/N]$. Its small-ball probability, together with the tracking failure probability, is $O(1/N)$. At $H$, the full residual contraction instead yields the stated high-probability fit.

At $\eta=1$, the positive logarithm $4(\log 2)3^T$ in Lemma A.6 dominates $896N^{64}$ at $M$ since $60\log 3>64$, and also at $H\ge M$ for large $N$. Thus $\mathrm{Var}(Y_T)\to\infty$ at either endpoint. Since $\|Z\|_2$ stays bounded, the triangle inequality $\|Y_T-Z\|_2\ge\sqrt{\mathrm{Var}(Y_T)}-\|Z\|_2$ gives the second divergence.

$\square$

**Lean proof.** [`early_degree`](../formal/CircleShortGDTails.lean#L230) · [`early_stopped_mse`](../formal/CircleDiscreteMoments.lean#L111) · [`early_fixed_limits`](../formal/CircleGDLimits.lean#L108) · [`ordinary_fit_forces_small`](../formal/CircleEarlyFit.lean#L90) · [`early_fit_probability`](../formal/CircleEarlyFit.lean#L211) · [`gaussian_horizon_fit`](../formal/CircleDiscreteMoments.lean#L95) · [`growing_variance_tendsto`](../formal/CircleEulerLimits.lean#L191) · [`unit_step_paired_divergence`](../formal/CircleEulerComparison.lean#L76)

**Conditioning on fit.** Conditioning on $\|f_H-y\|_N\le N^{-3}$ selects a deterministic endpoint. Conditioning on a hit by $H$ and returning the first hitting iterate selects a different random output. If a first-hit rule returns the $H$th iterate on a miss, Lemma A.6 gives divergent unconditional squared error for this rule as well. The escaping boxes are excluded under either success condition. Small conditional second moment under each of these two success laws remains open. [First-hit reduction](../formal/CircleConditioning.lean#L731) · [Divergence with fallback](../formal/CircleConditioning.lean#L887)

> **Corollary A.8 (A necessary width for bounded variance).** Under the hypotheses of Lemma A.6, if $\mathrm{Var}(Y_T)\le V$ with $V>0$, then $4(\log 2)3^T\le896m^2/\eta+\log V$. With $V$ fixed, bounded variance thus requires $m\gtrsim\sqrt\eta\,3^{T/2}$ as $T\to\infty$. More sharply, fix $0<\eta\le1$ and $c<\log 3$. Along any sequence of odd grids $N\ge3$, widths $m\ge1$ and integers $T\to\infty$ with $\log N=O(T)$ and $\log m\le cT$ eventually, both the variance and the same-seed squared error relative to $Z$ diverge.

**Proof idea.** Compare the logarithmic Gaussian probability cost with the cubic amplification exponent. Narrow boxes around trajectories of identical neurons reduce that cost to first order in the width.

**Proof.** Take logarithms in Lemma A.6 and use $4096m^3/(\pi^2\eta^2)\ge1$. For the sharper odd-grid conclusion, take two narrow boxes of opposite initial readout sign around configurations with identical neurons and initial radius independent of $m$. Gate clearance and relative-error induction through $T$ steps give a logarithmic probability cost $O_\eta(m(T+\log N+1))$ and squared-amplitude exponent $4(\log 2)3^T$. Under the stated hypotheses the cost is $O_\eta(Te^{cT})=o(3^T)$. The opposite-tail argument and the bounded reference second moment yield both divergences. The resulting restrictions on width are necessary for bounded variance.

$\square$

**Lean proof.** [`width_necessary`](../formal/CircleEulerLimits.lean#L347) · [`actual_lower`](../formal/CircleSynchronizedWidth.lean#L95) · [`divergence_below_log_three`](../formal/CircleSynchronizedWidth.lean#L189)

### Shrinking steps at fixed physical time

> **Corollary A.9 (Refinement at fixed time).** Fix $N\ge3$, $m\ge1$ and $t>0$. For integers $k\ge\max(1,\lceil t\rceil)$ let $Y_k$ be the mean after $k$ ordinary updates of size $t/k$. Then $\mathrm{Var}(Y_k)\to\infty$ and $\|Y_k-Y^{\mathrm{flow}}(t)\|_2\to\infty$ for every measurable equal-rate flow endpoint on the same seed.

**Proof idea.** As the step shrinks, the bad boxes move out into the Gaussian tail. Their terminal squared magnitude grows faster than their probability decays.

**Proof.** Substitute $\eta=t/k$ and $T=k$ in Lemma A.6. Then $L\propto\sqrt k$ and

$$
\mathrm{Var}(Y_k)\ge
\frac{4096m^3 k^2}{\pi^2t^2}
\exp\!\left[4(\log 2)3^k-896m^2k/t\right]\longrightarrow\infty .
$$

Flow dissipation bounds the parameter displacement by $\sqrt{tL_0}$, where $L_0$ is the initial loss. At fixed width the initial Gaussian has finite moments of every order, so the angular mean formula gives $\|Y^{\mathrm{flow}}(t)\|_2<\infty$. Apply the reverse triangle inequality as in Corollary A.7.

$\square$

**Lean proof.** [`fixed_time_variance_lower`](../formal/CircleEulerLimits.lean#L93) · [`fixed_time_variance_tendsto`](../formal/CircleEulerLimits.lean#L108) · [`rms_diverges_from_any_flow`](../formal/CircleEulerComparison.lean#L24)

Convergence of the discrete trajectories from an individual fixed seed to a selected ReLU flow remains open.

## Appendix. Selected Lean proofs

The following are complete declarations from the project sources. In these declarations, `n+1` is the grid size $N$, `score` is the initial deficit $X$, and `coefficient` is $c_N$. The functions `scaled` (GD) and `difference` (flow) both return $N^2\Delta$. The expression `(seedLaw m).real E` denotes the Gaussian probability of an event $E$ at width $m$. Lean writes “eventually” as `∀ᶠ`, and `Tendsto … atTop atTop` expresses divergence to positive infinity along the sequence. Each listing links to its source. The PDF attachment contains the proofs of the lemmas invoked in these scripts.

### Discrete gradient descent

The combined endpoint theorem records four conclusions. The first supplies a common fitting and tracking event and bounds the ordering error. The second gives convergence in probability. The last two give divergent unscaled mean-square error (`mse`) for the finite-grid and limiting slopes. The final three proof lines assemble these conclusions from the trajectory and moment estimates proved in the main text. [paired_discrete_gradient_descent](../formal/CirclePairedGDTheorem.lean#L59)

```lean
theorem paired_discrete_gradient_descent (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (odd : ∀ᶠ i in atTop, Odd (n i+1)) :
    (∀ᶠ i in atTop, FitsAndTracks (n i) ∧
      (seedLaw (gridWidth (n i))).real (CirclePairedGDEndpoint.miss (n i)) ≤
        (2+2*CircleScoreMargin.densityBound)/√((n i:ℝ)+1)) ∧
    (∀ ε : ℝ, 0<ε → Tendsto (fun i => (seedLaw (gridWidth (n i))).real
      {z | ε ≤ |scaled (n i) z - (π^2/40)*score (n i+1) (gridWidth (n i)) z|})
      atTop (𝓝 0)) ∧
    Tendsto (fun i => CirclePairedGDClocksTail.mse (n i+1) (horizon ((n i+1:ℕ):ℝ))
      1 (coefficient (n i))) atTop atTop ∧
    Tendsto (fun i => CirclePairedGDClocksTail.mse (n i+1) (horizon ((n i+1:ℕ):ℝ))
      1 (π^2/40)) atTop atTop := by
  refine ⟨?_,limiting_prediction n grow odd,CirclePairedGDClocksTail.horizon_predictions n grow odd⟩
  filter_upwards [grow.eventually fit_and_order,odd] with i h ho
  exact h ho
```

The rare-seed calculation gives an example of the induction inside the moment proof. At the symmetric initial state, `orbit` returns the pair $(A,W)$ of positive layer magnitudes. The slow and fast products $AW$ start equal. The one-step inequality `ratio_step` multiplies the cubed lower bound for their ratio by two. If that lower bound at step $t$ is $2^e$, its successor is $2^{1+3e}$. Since $3^t$ is odd, $e=(3^t-1)/2$ is an integer, and the script verifies its exact recurrence before applying the one-step estimate. [ratio_growth_exact](../formal/CirclePairedGDCenter.lean#L91)

```lean
theorem ratio_growth_exact {N m : ℕ} {η R : ℝ} (hN : 3≤N) (hm : 0<m)
    (hη : 0<η) (hR : 1≤R) (hlarge : 16*(32/η+32)≤R^2) (t : ℕ) :
    let S := orbit N m (1/2) η R t
    let F := orbit N m 2 η R t
    (2:ℝ)^((3^t-1)/2 : ℕ)*(S.1*S.2)≤F.1*F.2 := by
  induction t with
  | zero => simp [orbit_zero]
  | succ t ih =>
    let e := (3^t-1)/2
    have he : (3^(t+1)-1)/2 = 1+e*3 := by
      obtain ⟨k,hk⟩ := (show Odd ((3:ℕ)^t) from (by decide : Odd (3:ℕ)).pow)
      dsimp [e]
      rw [pow_succ]
      omega
    have h := CirclePairedGDScalar.ratio_step hη (qs_lower hN) (ys_bound hm N)
      hR hlarge t ((2:ℝ)^e) (by positivity) ih
    dsimp only
    rw [he,pow_add,pow_mul,pow_one]
    exact h
```

### Gradient flow

For each admissible flow pair `F`, `PairedBounds n F z` asserts fitting at both rates, grid RMS disagreement at most $2N^{-3}$, and tracking of the scaled population gap at seed $z$. The proof intersects the joint tracking event $A$ with the joint fitting event $B$, uses the union bound on their complements, and subtracts the two per-rate tracking errors using the common-seed identity. [common_event](../formal/CirclePairedTheorem.lean#L41)

```lean
theorem common_event (n : ℕ) (hn : 36864≤n+1) (ho : Odd (n+1)) (F : Rates n) :
    ∃ E : Set (Seed (Width n)), MeasurableSet E ∧
      (seedLaw (Width n)).real Eᶜ ≤ 96/((n:ℝ)+1)^158 ∧ ∀ z∈E, PairedBounds n F z := by
  obtain ⟨A,ma,pa,track⟩ := paired_likely_cap n 158 hn (by omega) ho F
  obtain ⟨B,mb,pb,fit⟩ := joint_fit_original_horizon n 158 hn (by omega) ho
  refine ⟨A∩B,ma.inter mb,?_,?_⟩
  · rw [compl_inter]
    exact (measureReal_union_le _ _).trans ((add_le_add pa pb).trans_eq (by ring))
  · intro z hz
    have f (q : Bool) := (fit z hz.2 _ (show benchmarkRate q=1/2 ∨ benchmarkRate q=1 ∨ benchmarkRate q=2 by
      cases q <;> norm_num [benchmarkRate]) ((F q).path z) ((F q).start z) ((F q).flow _ (Nat.cast_nonneg _) z)).1
    refine ⟨f,(norm_sub_le _ _).trans ((add_le_add (f false) (f true)).trans_eq (by ring)),?_⟩
    rw [identity,abs_mul,abs_of_nonneg (sq_nonneg _)]
    have b := endpointCap_le (n+1) 158 (by omega)
    push_cast at b
    have le := (abs_sub _ _).trans (add_le_add ((track z hz.1 false).trans b) ((track z hz.1 true).trans b))
    apply (mul_le_mul_of_nonneg_left le (sq_nonneg ((n:ℝ)+1))).trans_eq
    unfold errorCap
    field_simp; ring
```

The next declaration is unconditional. Its four conclusions give positivity of the finite-grid slope, its two-term expansion, RMS tracking of the scaled gap, and the ordering error probability including ties. The constants `trackingConstant` and `angularConstant` come respectively from the integrated path estimate and the spherical probability estimate. Dividing the RMS bound by $N^2$ gives the $O(N^{-15})$ error used in the signed expectation. [all_seed_bounds](../formal/CirclePairedTheorem.lean#L209)

```lean
theorem all_seed_bounds :
    ∀ᶠ n : ℕ in atTop, ∀ _ho : Odd (n+1), ∀ F : Rates n,
      0<coefficient n ∧
      |coefficient n-(π^2/40-π^4/(1600*((n:ℝ)+1)^2))|≤400/((n:ℝ)+1)^4 ∧
      sqrt (∫ z, (difference n (paths n F) z-coefficient n*score (n+1) (Width n) z)^2 ∂seedLaw (Width n))
        ≤ 2*CircleSharpMoments.trackingConstant/((n:ℝ)+1)^13 ∧
      (seedLaw (Width n)).real (miss n (paths n F)) ≤ (28+8*angularConstant/(π^2/80))/((n:ℝ)+1)^13 := by
  filter_upwards [eventually_ge_atTop 36864,actual_wrong_eventually] with n hn missb ho F
  exact ⟨coefficient_pos _,CircleCoefficientRemainder.uniform_remainder n,actual_scaled_rms n (by omega) ho F,missb ho F⟩
```

The elementary implication behind both ordering proofs is particularly short. If $DX\le0$ and $c>0$, expansion gives $(D-cX)^2-c^2X^2=D^2-2cDX\ge0$. Taking nonnegative square roots shows that an ordering error forces a prediction error of at least $c|X|$. The Lean proof squares both nonnegative sides and uses precisely those two sign conditions. [wrong_forces_error](../formal/CirclePairedOrdering.lean#L64)

```lean
private theorem wrong_forces_error {D X c : ℝ} (hc : 0<c) (h : D*X≤0) :
    c*|X|≤|D-c*X| := by
  apply (sq_le_sq₀ (mul_nonneg hc.le (abs_nonneg X)) (abs_nonneg _)).1
  rw [mul_pow,sq_abs,sq_abs]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hc.le h,sq_nonneg D]
```

Finally, the difference of the two expected population means is within $2C_{\mathrm{tr}}/N^{15}$ of $c_N/N^2$ by the per-rate estimate [signed_mean_finite](../formal/CirclePairedTheorem.lean#L234). Dividing the coefficient expansion by $N^2$ and adding the two errors proves that $\pi^2/(40N^2)-\pi^4/(1600N^4)$ predicts the signed shift to within $2C_{\mathrm{tr}}/N^{15}+400/N^6$. [signed_mean_expansion](../formal/CirclePairedTheorem.lean#L264)

```lean
theorem signed_mean_expansion (n : ℕ) (hn : 36864 ≤ n+1) (ho : Odd (n+1)) (F : Rates n) :
    let N := (n:ℝ)+1
    |(∫ z, trained n (F false) z - trained n (F true) z ∂seedLaw (Width n)) -
      (π^2/(40*N^2)-π^4/(1600*N^4))| ≤
      2*CircleSharpMoments.trackingConstant/N^15 + 400/N^6 := by
  intro N
  have hN : 0 < N := by dsimp [N]; positivity
  have coeff := div_le_div_of_nonneg_right (CircleCoefficientRemainder.uniform_remainder n)
    (sq_nonneg N)
  change |coefficient n - (π^2/40-π^4/(1600*N^2))| / N^2 ≤ 400/N^4/N^2 at coeff
  have bound : |(coefficient n-(π^2/40-π^4/(1600*N^2)))/N^2| ≤ 400/N^6 := by
    rw [abs_div, abs_of_pos (sq_pos_of_pos hN)]
    exact coeff.trans_eq (by ring)
  let M := ∫ z, trained n (F false) z - trained n (F true) z ∂seedLaw (Width n)
  calc
    |M-(π^2/(40*N^2)-π^4/(1600*N^4))| =
      |(M-coefficient n/N^2)+(coefficient n-(π^2/40-π^4/(1600*N^2)))/N^2| := by
        congr 1
        field_simp
        ring
    _ ≤ _ := (abs_add_le ..).trans (add_le_add (signed_mean_finite n hn ho F)
      bound)
```

## Appendix. Statement audit and trust model

The index `n` in the paired theorems denotes $N-1$. Each source location below points to the declaration that fixes the interpretation of a symbol in the statement. The two existence theorems show that the flow hypotheses can be satisfied for both rates on every grid used in the comparison. Both miss events count ties.

### Finite-grid gradient descent (Theorem 1)

For the two rates $0<\tau<\sigma$, Theorem 1 uses $\delta=\varepsilon=1/N$. The step satisfies $0<\eta\le2/(1+\sigma)$, and the common width is at least the larger of the two single-rate design widths.

| Paper object | Fully qualified Lean name | File and line | Meaning |
| --- | --- | --- | --- |
| Rate factor | `CirclePositiveSchedule.stretch` | [CirclePositiveSchedule.lean:20](../formal/CirclePositiveSchedule.lean#L20) | $\max(1,r)/r$ for hidden rate $r>0$. |
| Width $M_r(N)$ | `CirclePositiveSchedule.designWidth` | [CirclePositiveSchedule.lean:22](../formal/CirclePositiveSchedule.lean#L22) | Square of $N^8\lceil 3\cdot10^8\,\mathrm{stretch}(r)^2\rceil$. |
| Spectral gap bound $g_r$ | `CirclePositiveWidth.gap` | [CirclePositiveWidth.lean:29](../formal/CirclePositiveWidth.lean#L29) | $r/(\pi N)^2$. |
| Initial residual bound | `CircleFiniteWidth.R` | [CircleFiniteWidth.lean:24](../formal/CircleFiniteWidth.lean#L24) | $R(\delta)=\sqrt{12/\delta}$. |
| Residual tolerance | `CircleFiniteWidth.tol` | [CircleFiniteWidth.lean:30](../formal/CircleFiniteWidth.lean#L30) | $h=\min(N^{-3},\varepsilon/(2N^2))$. |
| Single-rate deadline | `CirclePositiveWidth.cap` | [CirclePositiveWidth.lean:35](../formal/CirclePositiveWidth.lean#L35) | Natural-number ceiling of $2\log(R(\delta)/h)/(\eta g_r)$. |
| Training RMS | `CircleWeightedDynamics.rms` | [CircleWeightedDynamics.lean:25](../formal/CircleWeightedDynamics.lean#L25) | Normalized grid residual norm after $t$ simultaneous updates. |
| Slope $c_N(\tau,\sigma)$ | `CircleRateDial.coefficient` | [CircleRateDial.lean:22](../formal/CircleRateDial.lean#L22) | $N^2(b_{\tau,N}-b_{\sigma,N})$. |
| Joint guarantee | `CircleRateDial.paired_gd` | [CircleRateDial.lean:53](../formal/CircleRateDial.lean#L53) | On every odd grid $N\ge3$, one event of probability at least $1-2/N$ controls both fits and the scaled gap error at every step from the larger deadline onward. |

### Model and reference

| Paper object | Fully qualified Lean name | File and line | Meaning |
| --- | --- | --- | --- |
| Seed space | `CircleEscapeBridge.Seed` | [CircleEscapeBridge.lean:71](../formal/CircleEscapeBridge.lean#L71) | Three real coordinates per neuron, in the order $a,w_1,w_2$. |
| Seed law | `CircleEscapeBridge.seedLaw` | [CircleEscapeBridge.lean:73](../formal/CircleEscapeBridge.lean#L73) | Product of $3m$ standard real Gaussian laws. |
| Grid node | `CircleEscape.gridPoint` | [CircleEscape.lean:224](../formal/CircleEscape.lean#L224) | Unit complex number at angle $2\pi i/N$, viewed in the real plane. |
| Activation | `CircleEscape.feature` | [CircleEscape.lean:27](../formal/CircleEscape.lean#L27) | Positive part of the real inner product. |
| Network | `CircleEscape.output` | [CircleEscape.lean:29](../formal/CircleEscape.lean#L29) | $c\sum_j a_j[w_j^\top x]_+$ with $c=1/\sqrt m$. |
| GD gate | `CircleEscape.gate` | [CircleEscape.lean:33](../formal/CircleEscape.lean#L33) | One at a positive preactivation and zero elsewhere. |
| Grid label | `CircleFlowPath.circleLabel` | [CircleFlowPath.lean:545](../formal/CircleFlowPath.lean#L545) | One plus the first coordinate of the input. |
| Residual vector | `CircleActualTracking.gridR` | [CircleActualTracking.lean:23](../formal/CircleActualTracking.lean#L23) | Grid residuals divided by $\sqrt N$, so the Euclidean norm is the RMS error. |
| Population mean | `CircleEscape.populationMean` | [CircleEscape.lean:210](../formal/CircleEscape.lean#L210) | Defined as $(c/\pi)\sum_j a_j\lVert w_j\rVert$. |
| Angular integral | `CircleAngularGeometry.real_angular_mean` | [CircleAngularGeometry.lean:54](../formal/CircleAngularGeometry.lean#L54) | Identifies this closed form with $(2\pi)^{-1}\int_0^{2\pi} f(x(u))\,du$. |
| Grid deficit $X$ | `CirclePairedCoefficient.score` | [CirclePairedCoefficient.lean:21](../formal/CirclePairedCoefficient.lean#L21) | One minus the initial grid mean. |
| Quadrature factor | `CircleSpectrum.weight` | [CircleSpectrum.lean:180](../formal/CircleSpectrum.lean#L180) | Constant-mode mass divided by that mass plus its grid aliases. |
| Reference $Z_\tau$ | `CircleEscapeBridge.reference` | [CircleEscapeBridge.lean:145](../formal/CircleEscapeBridge.lean#L145) | Initial population mean plus the quadrature factor times $X$. |
| Slope $c_N$ | `CirclePairedOrdering.coefficient` | [CirclePairedOrdering.lean:37](../formal/CirclePairedOrdering.lean#L37) | $N^2$ times the slow-minus-fast quadrature factor. |
| Endpoint $H$ | `CircleFlowTracking.horizon` | [CircleFlowTracking.lean:347](../formal/CircleFlowTracking.lean#L347) | Natural-number ceiling of $2\pi^2N^2\log(2\sqrt{12N}\,N^3)$. |
| Unit-step width | `CirclePairedGDEndpoint.gridWidth` | [CirclePairedGDEndpoint.lean:24](../formal/CirclePairedGDEndpoint.lean#L24) | $(n+1)^{32}$. |

### Dynamics and existence

| Paper object | Fully qualified Lean name | File and line | Meaning |
| --- | --- | --- | --- |
| Flow width | `CirclePairedTheorem.Width` | [CirclePairedTheorem.lean:23](../formal/CirclePairedTheorem.lean#L23) | $(n+1)^{32}$. |
| GD direction | `CircleWeightedStep.direction` | [CircleWeightedStep.lean:23](../formal/CircleWeightedStep.lean#L23) | Negative grid-loss gradient with hidden multiplier $\tau$, evaluated at the current state. |
| GD segment | `CircleWeightedStep.segment` | [CircleWeightedStep.lean:27](../formal/CircleWeightedStep.lean#L27) | Current state plus a scalar multiple of the simultaneous update direction. |
| GD trajectory | `CircleWeightedStep.iterate` | [CircleWeightedStep.lean:30](../formal/CircleWeightedStep.lean#L30) | Begins at the seed and takes a segment of length parameter $\eta$ at each update. |
| GD endpoint mean | `CircleWeightedDynamics.learnerMean` | [CircleWeightedDynamics.lean:27](../formal/CircleWeightedDynamics.lean#L27) | Population mean after the specified number of updates. |
| Flow path | `CircleFlowPath.IsFlow` | [CircleFlowPath.lean:189](../formal/CircleFlowPath.lean#L189) | Coordinatewise absolutely continuous, with weighted velocity given almost everywhere by admissible gates. |
| Flow learner | `CircleComparison.Learner` | [CircleComparison.lean:35](../formal/CircleComparison.lean#L35) | Starts at each seed, satisfies the flow predicate on every finite interval and has measurable endpoints. |
| Existence | `CircleComparison.learner_exists` | [CircleComparison.lean:41](../formal/CircleComparison.lean#L41) | Provides a learner for $N\ge3$ and $0<\tau\le2$. |
| Clarke selection | `CircleFlowConstruction.exists_borel_global_clarke_flow` | [CircleFlowConstruction.lean:75](../formal/CircleFlowConstruction.lean#L75) | Borel map into continuous paths with velocity in the essential gradient hull almost everywhere. |

### Events and error criteria

| Paper object | Fully qualified Lean name | File and line | Meaning |
| --- | --- | --- | --- |
| GD scaled gap | `CirclePairedGDEndpoint.scaled` | [CirclePairedGDEndpoint.lean:26](../formal/CirclePairedGDEndpoint.lean#L26) | $N^2$ times the slow-minus-fast GD contrast at unit step and $H$. |
| Flow scaled gap | `CirclePairedOrdering.difference` | [CirclePairedOrdering.lean:39](../formal/CirclePairedOrdering.lean#L39) | $N^2$ times the slow-minus-fast flow contrast at $H$. |
| GD miss | `CirclePairedGDEndpoint.miss` | [CirclePairedGDEndpoint.lean:29](../formal/CirclePairedGDEndpoint.lean#L29) | Scaled GD gap times $X$ is nonpositive. |
| Flow miss | `CirclePairedOrdering.miss` | [CirclePairedOrdering.lean:42](../formal/CirclePairedOrdering.lean#L42) | Scaled flow gap times $X$ is nonpositive. |
| Unit-step event | `CirclePairedGDTheorem.FitsAndTracks` | [CirclePairedGDTheorem.lean:21](../formal/CirclePairedGDTheorem.lean#L21) | One measurable event controls both fits and the scaled gap, with failure at most $2/\sqrt N$. |
| Flow event bounds | `CirclePairedTheorem.PairedBounds` | [CirclePairedTheorem.lean:32](../formal/CirclePairedTheorem.lean#L32) | Both fits, their grid RMS disagreement and the scaled prediction error at one seed. |
| GD squared error | `CirclePairedGDClocksTail.mse` | [CirclePairedGDClocksTail.lean:20](../formal/CirclePairedGDClocksTail.lean#L20) | Full-seed expectation of $(\Delta_T-dX/N^2)^2$ for the specified step and coefficient. |

**Trust model.** The Lean development is the proof of record. The prose explains the arguments. A reader can audit the correspondence by comparing the declarations above with the model and the reported theorem statements. In particular, Lean defines the population mean by the closed form and proves its equality with the angular integral. The formal guarantee rests on this correspondence, the Lean kernel and its foundational axioms, and the mathematical definitions used from Mathlib, including its Gaussian measures and integration. Kernel replay checks the proof terms, so a reader need not verify individual proof steps by hand. The numerical experiments have a separate reproducibility record.
