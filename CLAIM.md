# Interacting chiral SU(5) with three generations

## Comparator statement

At arbitrarily weak reference coupling, there exists a four-dimensional continuum SU(5) gauge theory with three generations of left-handed fermions in $\mathbf{10}\oplus\overline{\mathbf{5}}$. Its gauge-invariant Euclidean correlation functions satisfy reflection positivity and define a local relativistic quantum theory on a positive Hilbert space with unitary time evolution. In its vacuum, three-current correlations detect the handedness of both fermion representations, and a matter current from a single generation has a nonzero connected correlation with a gauge-field observable at spacelike separation. Along the lattice sequence defining this vacuum, the leading ultraviolet running coefficient tends to $43/3$, with gauge contribution $55/3$ and fermion screening $4$.

## Definitions used in the Lean statement

For every real lower bound $b$, there exists a four-dimensional SU(5) lattice history with fixed reference inverse squared gauge coupling $B_{\mathrm{ref}}>b$. Its matter content is three generations of left-handed fermions in $\mathbf{10}\oplus\overline{\mathbf{5}}$, where $\mathbf{10}$ is the exterior square of the defining representation. Along a selected sequence of increasing volume and cutoff depth, normalized lattice measurements yield a continuum theory of gauge-invariant observables in one vacuum.

The Euclidean correlations have positive semidefinite reflection matrices for finite families of the specified positive-slab observables in each coordinate direction. They continue to real-time vacuum correlations. On the reconstructed Hilbert space, the observable fields commute on their common invariant domain at spacelike separation. The proper orthochronous Poincaré group acts unitarily and strongly continuously, the joint energy–momentum spectrum lies in the closed forward light cone, and the cyclic unit vacuum spans the translation-invariant subspace. The stress tensor generates translations through its Ward identities. The prescribed three-current measurements in the $\mathbf{10}$ and $\overline{\mathbf{5}}$ channels recover their respective left-handed reference values to arbitrary accuracy on this same selected state.

There are compactly supported test functions $f$ and $h$ with spacelike-separated supports for which the prescribed first-generation matter current $J(f)$ and gauge-field clover observable $Q(h)$ satisfy

$$
\langle Q(h)\rangle=0,\qquad
\operatorname{Re}\!\left(\langle J(f)Q(h)\rangle-\langle J(f)\rangle\langle Q(h)\rangle\right)\ne 0.
$$

The brackets denote expectations in the reconstructed vacuum. $J$ and $Q$ are identified by their respective matter and gauge insertions in the lattice construction.

Write $B_{i,N}(j)$ for the fitted inverse squared gauge coupling at resolution $j$ on volume row $i$ with cutoff depth $N$ of this history. All rows have $B_{i,N}(0)=B_{\mathrm{ref}}$. Over $k$ steps toward the ultraviolet, let $\Delta B=B_{i,N}(j+k)-B_{i,N}(j)$. If $q_m$ is the stationary gauge charge at step $m$ toward coarser scales, the gauge increase in this window is $G=-\sum_{w=0}^{k-1}q_{N-1-j-w}$. Thus $G-\Delta B$ measures the screening after the finite-row fit correction.

The conversion to conventional coefficient units is $C_k(x)=(55/3)x/(k\ell_g)$. Here $\ell_g=[11C_A/(24\pi^2)]\log L>0$ depends only on the block ratio $L$ and the SU(5) color metric. The regulator uses $C_A=50$, giving $C_k(x)=(4\pi^2/5)x/(k\log L)$. The coefficients measured from the actual charges and fitted endpoints obey

$$
\forall\,\varepsilon>0\quad \exists\,J,K\ge 1\quad
\forall\,j\ge J,\ k\ge K,\quad \forall\,i\in\mathbb N,\ N\ge j+k:\qquad
\max\!\left\{
\left|C_k(G)-\frac{55}{3}\right|,
\left|C_k(G-\Delta B)-4\right|,
\left|C_k(\Delta B)-\frac{43}{3}\right|
\right\}<\varepsilon.
$$

The thresholds $J,K$ may depend on the selected history and the tolerance. They apply uniformly over volume rows and all cutoffs containing the window. Every fixed window is eventually covered along the selected sequence of volumes and cutoffs. The limit $43/3$ is the leading ultraviolet slope averaged over increasingly long logarithmic intervals beginning at increasingly fine scales.

The formal proposition is `ChiralSU5.InteractingThreeGenerationTheoryWithExactRunning`. The theorem submitted to Comparator is `ChiralSU5.exists_interacting_three_generation_theory_with_exact_running`.
