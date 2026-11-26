# The discrete gradient descent proof

Take an odd number $N\ge 3$ of equally spaced training angles $u_i=2\pi i/N$ on the unit circle. At angle $u$, the input is $x(u)=(\cos u,\sin u)$ and the label is $y(u)=1+\cos u$. Write $Q_N$ for the average on the training grid and $Q$ for the uniform average on the whole circle. Both averages of $y$ equal one.

A neuron with hidden weight $w_j\in\mathbb{R}^2$ computes $[w_j^\top x(u)]_+$, where $[v]_+=\max(v,0)$ is the rectified linear unit (ReLU). Its readout weight is $a_j\in\mathbb{R}$. The network with $m=N^{32}$ neurons predicts $f(u)=m^{-1/2}\sum_{j=1}^m a_j[w_j^\top x(u)]_+$. Draw all $3m$ coordinates independently from the standard normal distribution. Give this **same draw**, the seed, to both training runs.

For a grid vector $v$, its root mean square (RMS) is $\|v\|_N=(N^{-1}\sum_i v_i^2)^{1/2}$. Both runs minimize the loss $\frac12\|f-y\|_N^2$ by full-batch gradient descent (GD). Each update evaluates both layer gradients at the current weights, using ReLU derivative zero at the kink. It subtracts the readout gradient times a base step $\eta$ and the hidden gradient times $\eta\tau$. The slow run uses $\tau=1/2$, the fast run $\tau=2$. Write $f_{\tau,T}$ for the prediction after $T$ updates and $Y_{\tau,T}=Qf_{\tau,T}$ for its whole-circle mean. [Simultaneous update](../formal/CircleWeightedStep.lean#L23)

## The prediction at unit step

Let $\Delta_T=Y_{1/2,T}-Y_{2,T}$. Let $f_0$ denote the common initial prediction and $X=1-Q_N f_0$ the initial deficit on the grid. Set $\eta=1$ and return both networks at the deterministic update count

$$
H=\left\lceil 2\pi^2N^2\log\left(2\sqrt{12}\,N^{7/2}\right)\right\rceil .
$$

As $N$ grows through odd integers, changing the hidden learning rate produces a predictable difference in the final mean. For every fixed tolerance $\epsilon>0$,

$$
\Pr\!\left(\left|N^2\Delta_H-\frac{\pi^2}{40}X\right|\ge\epsilon\right)\longrightarrow 0.
$$

Both runs also fit the labels, meaning their training RMS residuals are at most $N^{-3}$, with probability tending to one. A positive deficit predicts a higher mean for the slow run, and a negative deficit predicts a higher mean for the fast run. Counting ties as misses, the probability of a miss is bounded by a constant times $N^{-1/2}$. All probabilities refer to the shared Gaussian seed. [Fit and ordering](../formal/CirclePairedGDTheorem.lean#L36) · [Limiting prediction](../formal/CirclePairedGDTheorem.lean#L47)

To measure mean-square error, square each seed's prediction error and average over the entire seed distribution. For the *unscaled* difference, this gives a divergent expectation.

$$
\mathbb{E}\!\left[\left(\Delta_H-\frac{\pi^2}{40N^2}X\right)^2\right]\longrightarrow+\infty .
$$

A small set of seeds makes the two runs separate fast enough to dominate this average. Both the prediction in probability and the divergence in mean square are formalized entirely in Lean for the actual simultaneous GD updates. [Complete discrete theorem](../formal/CirclePairedGDTheorem.lean#L59) · [Lean proof guide](proof-guide.md)

## Where the coefficient comes from

At initialization, the first derivative of the network prediction gives its sensitivity to each weight. Multiply the sensitivities at two angles coordinate by coordinate and sum, weighting the hidden coordinates by $\tau$. The result is the *empirical tangent kernel*. Its average over seeds is a deterministic kernel $k_\tau$. Let $K_\tau$ be the matrix with entries $k_\tau(u_i,u_j)/N$. Define $b_{\tau,N}=Qk_\tau(\cdot,0)/Q_Nk_\tau(\cdot,0)$. This ratio tells how much the mean on the whole circle moves per unit change in the grid mean under the linear training rule with the kernel held fixed. At zero training residual this rule predicts $Z_\tau=Qf_0+b_{\tau,N}X$. The common term cancels when the runs are subtracted. The difference is $c_NX/N^2$, where $c_N=N^2(b_{1/2,N}-b_{2,N})$ is positive and tends to $\pi^2/40$. [Coefficient and cancellation](../formal/CirclePairedOrdering.lean#L37) · [Coefficient limit](../formal/CircleLayerRates.lean#L29)

For a unit step the linear residual update is $I-K_\tau$, where $I$ is the identity. The eigenvalues of $K_\tau$ lie between $g_\tau=\tau/(\pi N)^2$ and $(1+\tau)/2$. At either hidden rate this gives $\lVert I-K_\tau\rVert\le 1-g_\tau$, where the norm is the largest possible expansion factor on grid vectors. The nonlinear estimate allows a smaller contraction rate $\kappa=15/[32(\pi N)^2]$ at both rates. [Unit-step contraction](../formal/CirclePositiveSpectrum.lean#L212) · [Nonlinear trajectory estimate](../formal/CircleWeightedDynamics.lean#L239)

For each rate, the initialization bounds fail with probability at most $\delta=N^{-1/2}$. They control the initial RMS residual by $\sqrt{12/\delta}$, the kernel entries and their population averages, and the weight carried by neurons close to a ReLU kink. During training the proof bounds each neuron's movement by $N^{-12}$ times its initial size. This keeps enough of the linear contraction to reach RMS residual at most $4N^{-97/32}$ at $H$. The change in population mean beyond the linear comparison contributes at most $N^{-4}$ in addition to the residual, giving $|Y_{\tau,H}-Z_\tau|\le 5N^{-97/32}$. [Initialization estimates](../formal/CirclePositiveConfidence.lean#L165) · [Residual at the training horizon](../formal/CirclePairedGDClock.lean#L52)

For all sufficiently large odd $N$, the two estimates hold together with probability at least $1-2/\sqrt N$. On that event both runs fit and

$$
\left|N^2\Delta_H-c_NX\right|\le 10N^{-33/32}.
$$

The proof uses $N-1\ge4^{32}$ as a sufficient cutoff for this joint estimate. The deficit has bounded second moment uniformly in $N$. Thus replacing $c_N$ by its limit preserves convergence in probability. To get the ordering, the proof also bounds the chance of a deficit too close to zero for the error bound to determine the sign. [Common event](../formal/CirclePairedGDTypical.lean#L208) · [Ordering from tracking](../formal/CirclePairedGDEndpoint.lean#L49) · [Passage to the limit](../formal/CirclePairedGDEndpoint.lean#L125)

## Why the squared error diverges

**Two exactly symmetric runs.** Fix any $\eta>0$ and choose $R\ge32$ with $R^2\ge16(32/\eta+32)$. Start every neuron at $(a_j,w_j)=(R,(R,0))$. Grid reflection and neuron permutation symmetry preserve the form $(sA,(sW,0))$, with magnitudes $A,W>0$ and a common sign $s=(-1)^t$ at update $t$. For the feature $h_s(u)=[s\cos u]_+$, put $q_s=Q_N h_s^2$ and $\beta_s=Q_N(yh_s)$. Grid geometry gives $q_s\ge1/16$ and $0\le\beta_s\le2$. The residual is $\sqrt m\,sAW h_s-y$. Substituting it into the two layer updates gives next magnitudes between $15/16$ and $17/16$ times their leading terms,

$$
A_{\mathrm{lead}}=\eta q_s AW^2,\qquad
W_{\mathrm{lead}}=\eta\tau q_s A^2W.
$$

Both signs flip and both magnitudes at least double, so the same estimates apply at the next step. Write $P_\tau=A_\tau W_\tau$ and $D_t=P_2/P_{1/2}$ at update $t$. Because both runs have the same sign, they use the same $q_s$. Consequently $D_0=1$ and $D_{t+1}\ge 4(15/17)^2D_t^3\ge 2D_t^3$. Iterating from one gives $D_T\ge 2^{(3^T-1)/2}$. [Exact symmetric update](../formal/CirclePairedGDGeometry.lean#L112) · [Magnitude estimates](../formal/CirclePairedGDScalar.lean#L53) · [Product separation](../formal/CirclePairedGDCenter.lean#L91)

**A positive-probability set of nearby seeds.** Measure the error of each readout coordinate relative to $A$ and the error of each hidden coordinate relative to $W$. Suppose every such error is at most $e\le 1/(8N)$. Each hidden dot product on the grid changes by at most $2eW$. Its magnitude in the symmetric state is at least $W/N$ because $|\cos u_i|\ge1/N$ on the odd grid. Every ReLU derivative therefore agrees between the two states at the start of this update. The grid predictions differ by at most $5e\sqrt m\,AW$. Subtracting the simultaneous gradients bounds the next absolute error by $eA+21e\eta AW^2$ for readouts and $eW+21e\eta\tau A^2W$ for each hidden coordinate. The next relative errors are at most $1024e$. [One-step perturbation estimate](../formal/CirclePairedGDTube.lean#L234)

For a return at step $T$, choose the box of seeds where each coordinate lies between its symmetric initial value and that value plus $1/(8N\,512^{2T})$. Its initial relative errors are at most $1/(8N\,1024^T)$. Iterating the one-step bound keeps both runs within relative error $1/(8N)$ through step $T$. For either run the signed population mean $sY_{\tau,T}$ then lies between $(\sqrt m/\pi)P_\tau/2$ and $(\sqrt m/\pi)2P_\tau$. At $T=t+1\ge2$, the fast product exceeds the slow product by a factor of at least eight. On this single box the actual output difference satisfies $|\Delta_T|\ge \sqrt m\,2^{3^t}$. [Box coordinates](../formal/CirclePairedGDCoordinates.lean#L15) · [Iteration through the horizon](../formal/CirclePairedGDShadow.lean#L23) · [Signed population means](../formal/CirclePairedGDBox.lean#L31) · [Actual output separation](../formal/CirclePairedGDBox.lean#L138)

**The expectation over the Gaussian seed.** Independent Gaussian coordinates give the box probability at least $\exp(-C_{N,m,T})$, with

$$
C_{N,m,T}=3m\left[(R+1)^2/2+\log(8\sqrt{2\pi}\,N)+2T\log512\right].
$$

Integrating the squared difference on that box gives $\mathbb{E}[\Delta_T^2]\ge\exp[(2\log 2/3)3^T-C_{N,m,T}]$. For any bounded deterministic coefficients $d_N$, set $G=d_NX/N^2$. Its RMS over seeds stays bounded, and $\mathbb{E}[(\Delta_T-G)^2]\ge\tfrac12\mathbb{E}[\Delta_T^2]-\mathbb{E}[G^2]$. This proves divergence whenever $3^T/[m(T+\log N+1)]\to\infty$. Every individual finite-step expectation exists. [Gaussian box probability](../formal/CircleSynchronizedWidth.lean#L59) · [Cost bound](../formal/CirclePairedGDCost.lean#L38) · [Finite moments](../formal/CirclePairedGDIntegrable.lean#L140) · [Mean-square subtraction](../formal/CirclePairedGDIntegrable.lean#L175) · [Divergence criterion](../formal/CirclePairedGDTail.lean#L97)

There is also a finite bound with the predictor already subtracted. Suppose $|d_N|\le B$ and $N^2\ge B(2+16R^2)$. Then for $T\ge2$,

$$
\mathbb{E}\!\left[\left(\Delta_T-\frac{d_NX}{N^2}\right)^2\right]\ge
\tfrac14\exp\!\left[\tfrac{2\log 2}{3}3^T-C_{N,m,T}\right].
$$

The grid-size condition bounds the prediction on the same box where the two outputs separate. [Finite lower bound](../formal/CirclePairedGDFiniteTail.lean#L35)

At width $m=N^{32}$, every schedule with $T\ge60\log N$ eventually satisfies the criterion. This includes $\lceil60\log N\rceil$, $H$, and $\lceil H/\eta\rceil$ for fixed $\eta>0$. The fitting and ordering result above concerns the deterministic endpoint $H$ at $\eta=1$. The mean-square error conditional on both runs fitting there remains open. [General late schedule](../formal/CirclePairedGDClocksTail.lean#L37) · [Logarithmic return](../formal/CirclePairedGDClocksTail.lean#L56) · [Return at physical time](../formal/CirclePairedGDClocksTail.lean#L64)
