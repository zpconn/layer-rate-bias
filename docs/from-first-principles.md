# The learning-rate prediction from first principles

Two networks can fit the same labeled points on a circle and still give different averages between those points. In this construction, the mean prediction at initialization tells us how the final average will respond to a change in the hidden-layer learning rate. The calculation starts with the difference between the mean on a finite grid and the mean around the whole circle. [Paper](../paper/paper.pdf) · [Lean proof guide](proof-guide.md)

## Two ways to average around a circle

An angle $u$ specifies the input $x(u)=(\cos u,\sin u)$ on the unit circle. Let $N\ge3$ be odd. The **training grid** consists of the $N$ angles $2\pi i/N$ for integers $i$ from zero to $N-1$. The **teacher** is the function that supplies the target value, or label, at each input. Here it gives $y(x(u))=1+\cos u$.

For a prediction function $f$, let $Q_N f$ be its **grid mean**, the arithmetic average of its predictions at those $N$ inputs. Let $Qf$ be its **population mean**, the average of $f(x(u))$ when $u$ is uniform on $[0,2\pi)$. The cosine averages to zero in both cases, so the grid and population means of the teacher are both one.

## How the two runs train

A network of **width** $m$ combines $m$ simple functions, called hidden units. These units form the **hidden layer**. Unit $j$ has a two-dimensional hidden weight $w_j$. For an input $x$ it takes the dot product $w_j^\top x$ and retains its positive part. Write $[v]_+=\max(v,0)$ for this operation, called the rectified linear unit (ReLU). The resulting value $[w_j^\top x]_+$ is the unit’s **activation**. A scalar **readout weight** $a_j$ determines how much that activation contributes to the prediction. The **readout layer** combines the weighted activations as a single output. Collecting the weights into a vector $\theta$ gives the network

$$
f_\theta(x)=\frac{1}{\sqrt m}\sum_{j=1}^m a_j[w_j^\top x]_+ .
$$

Draw each of the $3m$ weight coordinates independently from a normal distribution with mean zero and variance one. One complete draw is a **seed**. Start both networks from the same seed, so that their initial prediction function $f_0$ is identical. The **initial deficit** is $X=1-Q_N f_0$. A positive value means that the initial predictions average too low on the grid. Repeating the experiment with fresh seeds supplies the randomness for all probabilities and expectations below.

Training adjusts both layers. The difference between a prediction and its label at a training input is its **residual**. Average the squared residuals across the grid. The square root of this average is the **root mean square** (RMS) training error. Half the average is the **loss** $L(\theta)$ that training aims to reduce. A network **fits** when that error is at most $N^{-3}$.

Where the loss is differentiable, its gradient is the vector of derivatives with respect to all weights. Both training rules use all $N$ examples to compute it, hence **full-batch** training. In **gradient descent** (GD), each update computes the gradient at the current weights and moves all weights simultaneously in the negative gradient direction. In **gradient flow**, the negative gradient determines a continuous velocity. Both rules multiply the readout component of the gradient by one and the hidden component by a factor $\tau$, the **relative hidden-layer rate**. GD uses a base step of one. Within each training rule we compare two runs, one with $\tau=1/2$ and the other with $\tau=2$.

The ReLU has a kink where a hidden unit’s dot product is zero. GD uses derivative zero there. For flow, the Clarke subdifferential of the loss is the closed convex hull of limits of gradients at nearby differentiability points. An allowed flow path is absolutely continuous, so its velocity integrates to the change in weights. Almost everywhere in time its velocity is a negative vector from that subdifferential, weighted by the two layer rates. Such paths exist. The flow result holds for every choice that is Borel measurable in the seed, which lets us assign probabilities to its outcomes. [Flow construction](../formal/CircleFlowConstruction.lean#L75)

## The prediction

To state the result, set $m=N^{32}$ and let $N$ grow through odd integers. Choose the common training endpoint $H$ by the formula below. The logarithm is natural, and the ceiling rounds up to an integer.

$$
H=\left\lceil 2\pi^2N^2\log(2\sqrt{12}\,N^{7/2})\right\rceil .
$$

For GD, take $H$ updates. For flow, train until time $H$. Within either experiment, let $Y_\tau$ be the network’s population mean at that endpoint. The slower hidden layer corresponds to $Y_{1/2}$, the faster to $Y_2$. The prediction for their difference is

$$
Y_{1/2}-Y_2 \;\approx\; \frac{\pi^2}{40}\,\frac{X}{N^2}.
$$

An initial deficit above zero predicts that the slower rate gives the higher final mean. A deficit below zero reverses the ordering. Both networks fit with probability tending to one. Both theorems, starting from the actual weight updates for GD and the actual training paths for flow, are formalized entirely in **Lean**, a system for checking mathematical proofs. The difference between their **signed population-mean errors**, $Y_{1/2}-1$ and $Y_2-1$, is exactly the displayed left-hand side. Thus we can choose the rate predicted to give the higher or lower signed error. Which choice brings the mean closer to one also depends on where both means lie. [Discrete GD theorem](../formal/CirclePairedGDTheorem.lean#L59) · [Flow theorem](../formal/CirclePairedTheorem.lean#L221)

We can measure the true population mean without drawing any new inputs. Write $\lVert w_j\rVert$ for the Euclidean length of the hidden weight. Rotating it into the horizontal direction leaves its uniform angular average unchanged. The positive part of a cosine integrates to two over one turn. Consequently, for any weights,

$$
Qf_\theta=\frac{1}{\pi\sqrt m}\sum_{j=1}^m a_j\lVert w_j\rVert .
$$

This identity measures a network’s mean at any stage of training. Predicting that mean *in advance* requires understanding what training does to the weights. [Angular integral](../formal/CircleAngularGeometry.lean)

## Where the coefficient comes from

At a point of differentiability, a small weight change alters a prediction to first order by its gradient dotted with that change. For two inputs, take the inner product of their prediction gradients with weight one on the readout coordinates and $\tau$ on the hidden coordinates. The result is the **tangent kernel** between those inputs. It describes how a training residual at one input influences the prediction at the other. The actual kernel changes as the weights move. Evaluate it at initialization and average its entries over seeds to obtain a fixed, deterministic kernel.

Using this fixed kernel throughout training gives a linear prediction rule. Start the rule at the actual $f_0$ for the seed in question and let it reach exact agreement with the labels on the grid. Write $Z_\tau$ for the resulting population mean, the **reference** for a network trained at rate $\tau$. Grid rotation leaves the kernel unchanged, so every grid point has the same influence on this mean. Write $b_{\tau,N}$ for the fraction of the initial grid-mean deficit that passes into the population mean. Then

$$
Z_\tau=Qf_0+b_{\tau,N}X,\qquad
Z_{1/2}-Z_2=(b_{1/2,N}-b_{2,N})X.
$$

The common term $Qf_0$ cancels because the two networks start with the same weights. To find $b_{\tau,N}$, decompose functions of the angle into waves with an integer number of cycles per turn. That integer is the angular frequency. The average around the circle keeps only the constant part, at frequency zero. Sampling only the grid also counts certain oscillations as constant. For example, $\cos(2Nu)$ equals one at every grid point but averages to zero around the circle. In this kernel the nonzero frequencies that contribute to the grid’s constant part are $k=\pm 2Nj$ for positive integers $j$. [Grid frequencies](../formal/CircleGridSpectrum.lean) · [Kernel identification](../formal/CircleKernelIdentification.lean)

Two positive sums, $A_N$ and $B_N$, collect the contributions of these frequencies. In each summand put $k=2Nj$. The factor two includes the negative frequency as well.

$$
A_N=2\sum_{j\ge1}\frac{1}{(k^2-1)^2},\qquad
B_N=2\sum_{j\ge1}\frac{k^2}{(k^2-1)^2}.
$$

The kernel calculation gives $b_{\tau,N}=1/(1+A_N+\tau B_N/(2+\tau))$. Both sums approach zero as $N$ grows, and $N^2B_N$ approaches $\pi^2/12$. The factor $\tau/(2+\tau)$ is $1/5$ for the slower hidden layer and $1/2$ for the faster one. The slower run therefore passes a larger fraction of $X$ into its mean. Define the **finite-grid coefficient** by $c_N=N^2(b_{1/2,N}-b_{2,N})$. It is positive for every odd $N\ge3$. Its limit is

$$
\left(\frac12-\frac15\right)\frac{\pi^2}{12}=\frac{\pi^2}{40}.
$$

The reference difference is exactly $c_N X/N^2$. Moving from that identity to the trained-network prediction requires bounding the errors $Y_\tau-Z_\tau$ on actual training runs. [Exact finite-grid coefficient](../formal/CircleFiniteCoefficient.lean#L88)

## How accurate is the prediction?

Let $\mathbb{E}$ denote expectation over the random seed. For any random error $U$, its **mean-square error** is $\mathbb{E}[U^2]$, and its RMS is the square root of that quantity. These averages include *all* seeds. A high-probability bound can instead hold on a set of seeds whose probability approaches one. We write $O(N^{-p})$ for a magnitude bounded by a constant times $N^{-p}$ for all sufficiently large odd $N$. The constants in these bounds are independent of $N$.

**Discrete GD.** Define the scaled difference $D=N^2(Y_{1/2}-Y_2)$. For all sufficiently large odd $N$, one set of seeds has probability at least $1-2/\sqrt N$. On every seed in this set both runs fit after exactly $H$ updates and

$$
|D-c_NX|\le 10N^{-33/32}.
$$

The proof bounds how far the actual weights move and follows the residual through each update. At $H$ the residual’s grid RMS in each run is at most $4N^{-97/32}$, and each population mean is within $5N^{-97/32}$ of its reference. Subtracting the two references gives the displayed bound. [Joint fitting and tracking](../formal/CirclePairedGDTypical.lean) · [Unit-step trajectory](../formal/CircleWeightedDynamics.lean)

A wrong ordering, counting a tie as a miss, means $DX\le0$. On the shared event this can happen only for an initial deficit within $10N^{-33/32}/c_N$ of zero. The chance of drawing such a deficit is bounded by a constant times the interval width. Including the event’s failure probability gives $\Pr(DX\le0)=O(N^{-1/2})$. Replacing $c_N$ by $\pi^2/40$ gives convergence **in probability**. For every fixed positive tolerance, the chance that $|D-(\pi^2/40)X|$ reaches that tolerance tends to zero. [Discrete ordering and limiting prediction](../formal/CirclePairedGDTheorem.lean#L59)

Other seeds make the two runs separate extremely quickly. For example, start all neurons with the same large readout and the same horizontal hidden weight. In each run, multiply the absolute readout weight by the length of the hidden weight. At each update the ratio of the fast product to the slow product grows to at least twice the cube of its old value. A small box of initial weights around this symmetric configuration has positive Gaussian probability. On the whole box, the two population means diverge from one another fast enough to dominate the average of the squared prediction error. For $d_N=c_N$ or $d_N=\pi^2/40$, the unscaled mean-square error satisfies

$$
\mathbb{E}\!\left[\left(Y_{1/2}-Y_2-d_N X/N^2\right)^2\right]\longrightarrow\infty.
$$

Each finite network at each finite step has a finite mean-square error. The divergence is a limit as the grid and width grow. [Separation of the symmetric runs](../formal/CirclePairedGDCenter.lean) · [Nearby Gaussian seeds](../formal/CirclePairedGDBox.lean) · [Integrability](../formal/CirclePairedGDIntegrable.lean) · [Mean-square divergence at the specified clock](../formal/CirclePairedGDClocksTail.lean)

**Gradient flow.** Both networks fit on the same set of seeds with probability $1-O(N^{-158})$. On that set their predictions differ on the grid by at most $2N^{-3}$ in grid RMS. With an initial deficit bounded away from zero in magnitude, the difference in their population means on the theorem’s common event is at least a constant times $N^{-2}$. The population shift can therefore be larger than the entire grid RMS disagreement. [Joint fit](../formal/CirclePairedTheorem.lean#L41) · [Separation on a fixed margin](../formal/CirclePairedTheorem.lean#L146)

Over all seeds, each error $Y_\tau-Z_\tau$ has RMS at most a constant times $N^{-15}$. Subtract the two means and rescale by $N^2$. The RMS error of $N^2(Y_{1/2}-Y_2)-c_N X$ is then $O(N^{-13})$. For the finite grid, $c_N=\pi^2/40-\pi^4/(1600N^2)+O(N^{-4})$. Replacing $c_N$ with $\pi^2/40$ gives an RMS error of order $N^{-4}$ in the original, unscaled mean difference. Counting a trained tie as a miss, the probability of predicting the wrong ordering is $O(N^{-13})$. [All-seed error and ordering](../formal/CirclePairedTheorem.lean#L209) · [Leading RMS error](../formal/CirclePairedSecondOrder.lean#L93)

The proof compares the actual kernel along the flow with its fixed reference kernel. For most seeds the two kernels start close, and at any given training input only a small fraction of units can switch between zero and positive activation. This controls how much the kernel changes and hence how far the actual population mean can depart from the reference. For exceptional seeds the decrease in loss bounds the movement of the weights. The proof uses that movement bound to keep even their contribution to the RMS small. [Tracking along the path](../formal/CircleSharpTracking.lean) · [Integration over all seeds](../formal/CircleSharpMoments.lean#L159)

Averaging a trained model’s signed population-mean error over seeds gives its **statistical bias**, $\mathbb{E}[Y_\tau]-1$. For flow, the initial readout weights are independent of the hidden weights and have mean zero, so $\mathbb{E}[Q_N f_0]=0$ and $\mathbb{E}[X]=1$. The absolute value of the expected difference from the finite-grid prediction is bounded by its RMS. It follows that the difference in the flow biases is $\mathbb{E}[Y_{1/2}]-\mathbb{E}[Y_2]=c_N/N^2+O(N^{-15})$, positive for all sufficiently large odd $N$. For GD, squaring an error discards its sign, so the divergence result leaves the corresponding expected signed difference unresolved. [All-seed flow estimate](../formal/CirclePairedTheorem.lean#L209) · [Discrete scope](paired-discrete-gd.md)

In a smaller numerical test, $N=3$, $m=32{,}768$ and $c_3\approx0.239159$, compared with $\pi^2/40\approx0.246740$. Each pair used a numerical approximation to the two flows at a shorter training time than $H$. The initial deficit correctly predicted the observed ordering for 48 of 48 pairs under ordinary Gaussian sampling and 46 of 48 pairs sampled by retaining only seeds with $X<0$. Both misses had $X$ close to zero. [Figure and data](../layer-rates/README.md) · [Empirical checks in Lean](../formal/CirclePairedData.lean)

## How long you train also matters

In a separate comparison, give both layers rate one. Observe flow at elapsed time $T$ and GD after $T$ unit updates. Write $Y_T$ for either run’s population mean at that endpoint. Its bias is $\mathbb{E}[Y_T]-1$. Its **variance** $V_T=\mathbb{E}[(Y_T-\mathbb{E}[Y_T])^2]$ measures how much the population mean varies between independent initializations. The same-seed kernel reference for these equal rates is $Z_1$.

Consider two early endpoints, $S=\lceil\pi^2\log N\rceil$ and $M=\lceil60\log N\rceil$, before the common long endpoint $H$. At $S$ the reference predicts limits for the bias multiplied by $N^2$ and the variance multiplied by $N^4$. Both actual algorithms have these limits.

$$
N^2(\mathbb{E}[Y_S]-1)\longrightarrow-\frac{\pi^2}{36},
\qquad
N^4V_S\longrightarrow\frac{7\pi^2}{1620}.
$$

| Endpoint | Gradient flow | Unit-step GD |
|---|---|---|
| $S$ | The scaled bias and variance have the displayed limits. | The same two limits hold. For both algorithms the probability of a fit at $S$ is $O(1/N)$. |
| $M$ | The RMS difference from $Z_1$ decays faster than $N^{-2}$. | Both $V_M$ and $\mathbb{E}[(Y_M-Z_1)^2]$ diverge. For both algorithms the probability of fitting by $M$ is still $O(1/N)$. |
| $H$ | The network fits with high probability, the RMS difference from $Z_1$ is $O(N^{-15})$ and both scaled limits still hold. | The network fits with high probability, and both unscaled quantities from the preceding row still diverge. |

Each column observes the same run at three successive endpoints. The divergence occurs as the grid grows. At fixed $N$, the moments are finite after each finite number of steps. At $S$, a slowly decaying wave in the residuals around the grid keeps most models from fitting, even though the population mean already has the two reference limits. [Flow moments](../formal/CircleSharpMoments.lean) · [Discrete limits](../formal/CircleGDLimits.lean) · [Early fitting probability](../formal/CircleEarlyFit.lean) · [Divergence](../formal/CircleEulerLimits.lean)

### What happens to rare runs

Under equal-rate flow, write $\theta_t$ for the weights at elapsed time $t$. The loss decrease bounds how far the weights can move from their initial value $\theta_0$ by $\lVert\theta_t-\theta_0\rVert\le\sqrt{tL(\theta_0)}$. Together with the angular-mean formula, this controls the **fourth moment** $\mathbb{E}[|Y_H-Z_1|^4]$ even on unusual trajectories. Let $B$ be the event on which the usual comparison with the kernel fails, and $\Pr(B)$ its probability. Hölder’s inequality bounds the contribution of those seeds to the RMS by $\mathbb{E}[|Y_H-Z_1|^4]^{1/4}\Pr(B)^{1/4}$. [Flow path identities](../formal/CircleFlowPath.lean) · [Fourth moment](../formal/CircleFlowMoments.lean#L407) · [Tracking](../formal/CircleSharpTracking.lean)

A discrete update can instead amplify large initial weights. The ReLU’s derivative acts as a **gate** equal to one for a positive dot product and zero otherwise. In the readout update each residual multiplies an activation. In the hidden update it multiplies the readout weight, the gate and the input. The proof identifies two boxes of seeds by restricting the initial coordinates to intervals. Within each box, all readouts share a sign. Write $s$ for a lower bound on every readout magnitude and hidden-weight length, and put $L_*=8\sqrt m$. A unit update flips the common sign and makes $s^3/L_*^2$ a lower bound for the new magnitudes and lengths. The same inequality applies at the next update. The two boxes have opposite signs at any given endpoint, so at least one produces values far from the overall mean. At the middle and long endpoints this gives the variance lower bound

$$
V_T\ \ge\
\frac{4096m^3}{\pi^2}
\exp\!\left(4(\log 2)3^T-896m^2\right).
$$

The negative term $896m^2$ comes from the small probabilities of the boxes. In the positive term at $M$, we have $3^M\ge N^{60\log 3}$ and $60\log 3>65$, whereas $m^2=N^{64}$. The growth in the outputs outstrips the probability cost. Since $\mathbb{E}[Z_1^2]$ stays bounded, the divergence also forces $\mathbb{E}[(Y_T-Z_1)^2]$ to grow without bound at $M$ and $H$. [One-step growth](../formal/CircleGridEscape.lean) · [Endpoint bounds](../formal/CircleEulerLimits.lean)

One can also **condition on fitting**, meaning average only over seeds whose networks meet the training tolerance. The two boxes that prove divergence always miss that tolerance. Among runs fitted at $H$, the open question is whether *other* rare seeds produce large enough errors to affect the conditional mean-square tracking rate. Stopping as soon as the tolerance is first reached by $H$ gives a second open version, since later updates can change the returned network. [Fit and stopping rules](../formal/CircleConditioning.lean)
