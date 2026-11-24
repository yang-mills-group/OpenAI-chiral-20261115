import YM.CF.Fixed.Extensive
import YM.CF.Fixed.PastBound
import YM.CF.Fixed.ShellAngle

/-!
Audit on the **same** background. Applies with the supplied sigma cap
receipt and any paid Book (PathData etc providable). Constants used later
will be BEFORE volume and even BEFORE fixed coupling value. The exponents
here are at the final block, not startup. Leak bound relative to genuine
gauge × fermion scale `(drip ...)`, extending Core.cents. The weaker part is
that this is still a `flag vs ALL Lace exp-volume` estimate. Don't misread the
vacuum as positive; the `drip` lower here must still be matched to the actual
partition by a **small** error. This is an extensive relative reference bound
incl upper. When in the volume charge regime of phase normalization we can use
it to improve volume window. Constants could usefully be optimized.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Fixed.Extensive
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial Nacre Font Laic Graph Skye Wilson MeasureTheory Paige Vault Pivots RG Emu Flare
open Sods Vale Nova
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
variable {α:Type*}{m B N L:Side}{j n:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e v b c a l r K u η vA k s r' D L' C μ y R w z kL β h c' :ℝ}{P:Grasp Y B e}{hP:Pearl P}
variable (V:GramM (mid m B))(S:Loom (mid m B))
variable (Q: Pic.Span hP K b v c l r' n)(H:SkinT V S e)
include H Q
local notation "N_" => mid m B
local notation "kBB" => V.beta
local notation "P_" => V.p.threshold
local notation "G_" => More N_
variable (W:Ledger R u η r C V)(Y': V.path.Bounds V.funds μ D L')
variable (a_:0≤r)(h_:1≤R)(i_:0<z)(e_:2*kL≤ V.beta* (V.funds.direct*z^2/2))(f_:2*kL≤ V.beta*(V.funds.linear*V.p.threshold*z))(p_:0<kL)(t_:0≤V.beta)(w_:0≤w)(vL:w≤V.funds.linear)
include W Y' a_ h_ i_ e_ f_ p_ t_

omit Y' i_ e_ f_ p_ t_ in
lemma mile_charge (T:Orbit N_)(Z:ℝ) (g:n≤ (N_).val)(hp: past V T.1 ≤ Real.exp Z * diminish z kL T.1): ‖recX P V S T‖ ≤ Real.exp (chargeE N_ u η C + Z)*diminish z kL T.1 := by
  obtain ⟨d,q,F⟩:=H.wave
  have hh:=(P.broadness _ (Q.plan m g).1 V.J.M).projection (S T) (F.paid T); let Z':=past V T.1; have hx:0≤ Z':=(Real.exp_pos _).le
  let P':= cab V P S T; have hg:‖P'‖=1:=(sea_g (Q.plan m g).1 (S T) (F.paid T) V.J.M).2
  have he: ‖beam V P S T‖ ≤ Real.exp (chargeE N_ u η C):=(spentS _ _ P').trans (by rw [hg,mul_one]; exact flag_charge W _ a_ h_ hh)
  rw [porch,norm_smul,Real.norm_of_nonneg hx]; exact (mul_le_mul hp he (norm_nonneg _) (hx.trans hp)).trans_eq (by rw [Real.exp_add]; ring)

lemma mile_global (T:Orbit N_)(g:n≤ (N_).val) : ‖recX P V S T‖ ≤ Real.exp (chargeE N_ u η C + totalTitle G_ kL P_ kBB D L') * diminish z kL T.1 := by
  apply mile_charge V S Q H W a_ h_ T _ g
  exact dim_title z _ kL i_.le p_.le T.1 (ownTitle i_ Y' t_ (le_trans (by linarith only [p_]) e_) (le_trans (by linarith only [p_]) f_) p_.le T.1)

include w_ vL
local notation "Z_" => chargeE N_ u η C + flagTitle G_ kL P_ kBB w D L'
lemma mile_flag (T:Orbit N_)(g:n ≤ (N_).val)(hx:T∉ Lace V) : ‖recX P V S T‖ ≤ Real.exp (Z_)* diminish z kL T.1 := by
  apply mile_charge V S Q H W a_ h_ T _ g; exact dim_title z _ kL i_.le p_.le T.1 (earnFlag i_ Y' t_ p_.le e_ f_ w_ vL T.1 (fun h=>hx h)) -- maybe implicit order

-- old road_b no drip. improvement by two different savings. Here z liquor.
lemma road_ext(g:n ≤ (N_).val)(O:Opt (α:=α) N_)(hp:‖Emu.gain O.R‖ ≤ (mid m B).val^2)(T:Orbit N_)(hYA:T∉ Lace V):
    ‖recW O P V S T-baseW O P V S T‖ ≤ (lite O *Real.exp (Z_))* diminish z kL T.1:=by
  have he:=mile_flag V S Q H W Y' a_ h_ i_ e_ f_ p_ t_ w_ vL T g hYA
  unfold baseW recW; rw [Graph.dim,Set.indicator_of_notMem hYA,zero_smul,sub_zero, mul_assoc]; exact (earn O _ _ hp).trans (mul_le_mul_of_nonneg_left he (by unfold lite; positivity))

omit w_ vL W H Q a_ h_ i_ p_ f_ t_ e_ Y'
local notation "Xμ" => shellMass group z

def lowerBook(n:Side)(u Z K:ℝ):= (shellMass group u)^(cotree (More n)).card * Real.exp (-Z)*Real.exp (-(n.val:ℝ)^4*K)
def upperBook(n:Side)(u k Z:ℝ):= (k*shellMass group u)^(pivots (More n)).card * Real.exp Z

def volumeBand (n:Side)(u B C Z Z' : ℝ):=
    4*(More n).val^4 * Real.log B + Z + Z' + (n.val:ℝ)^4*C - 4*Real.log (shellMass group u)
lemma lowerBook_pos (T A:ℝ)(g:0<z)(h:z≤1)(n:Side):0 < lowerBook n z T A := by unfold lowerBook; have he:= shellMass_pos group g h; positivity
lemma upperBook_pos (T A:ℝ)(t:0<A)(g:0<z)(h:z≤1)(n:Side):0 < upperBook n z A T := by unfold upperBook; have he:= shellMass_pos group g h; positivity
lemma comparison (A c u Z Z':ℝ)(h:0<u)(hu:u≤1)(x:1 ≤ A)(n:Side):
    upperBook n u A Z / lowerBook n u Z' c ≤ Real.exp (volumeBand n u A c Z Z') := by
  let N:=More n; let r:= shellMass group u; have hT:0<r:= shellMass_pos group h hu; have hs:r≤1:= shellMass_le ..; have hA:0<A:=zero_lt_one.trans_le x
  let d:=(pivots N).card; let k:=(cotree N).card; let g:=(generators N).card
  have he:k=g+d:=by
    have ht:= (all_count (N:=N)); have hx:= Finset.card_compl_add_card (treeLinks N)
    rw [show Fintype.card (Link N)=4*N.val^4 from (by unfold Link Edge; rw [Fintype.card_prod,site_card,show Fintype.card Axis=4 from rfl,Nat.mul_comm])] at hx; change k+(treeLinks N).card=_ at hx; change _+g+d=_ at ht; omega
  have hy: (d:ℝ) ≤ 4*(N.val:ℝ)^4:=by exact_mod_cast (show d≤4*N.val^4 from le_trans (Nat.le_add_left _ _) (Eq.le (all_count (N:=N))))
  have hv : -Real.log r ≥ 0:=neg_nonneg.mpr (Real.log_nonpos hT.le hs)
  let F:=upperBook n u A Z / lowerBook n u Z' c; have hF:0<F:=div_pos (upperBook_pos Z A hA h hu n) (lowerBook_pos Z' c h hu n)
  change F ≤ _; nth_rw 1 [← Real.exp_log hF]; apply Real.exp_le_exp.mpr
  unfold F upperBook lowerBook; have hx':0< r^k:=pow_pos hT _; have hp:0< (A*r)^d:=by positivity
  change Real.log (((A*r)^d* Real.exp Z)/(r^k*Real.exp (-Z')* Real.exp _)) ≤ _
  rw [Real.log_div (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity)]; simp only [Real.log_exp, Real.log_pow]; rw [Real.log_mul hA.ne' hT.ne',he]; push_cast; unfold volumeBand
  have hx:= Real.log_nonneg x; have hg:(g:ℝ)≤4:=by exact_mod_cast (pin_le (N:=N))
  nlinarith

lemma dim_integral (z k:ℝ)(h:ℝ) (T: (∫ x:SU.E,saltWeight group z k x∂group.probHaar)≤h):
    Integrable (fun x:Orbit N=>diminish z k x.1) (city N) ∧ ∫ x:Orbit N,diminish z k x.1 ∂city N ≤ h^(pivots (More N)).card:=by
  have he:MeasurePreserving (Prod.fst:Orbit N→ Pane N) (city N) (prior group (More N)) := measurePreserving_fst
  have hv: Measurable (diminish (N:=More N) (G:=group) z k):= (dim_cont ..).measurable -- frobenius instance? measurable
  refine ⟨(integrable_dim z k).comp_fst (depot N),?_⟩; rw [← integral_map_of_stronglyMeasurable he.measurable hv.stronglyMeasurable,he.map_eq]; exact mass_dim T

include Y' Q i_
local notation "X_" => stoutY G_ kBB (4*z) h P_ D L'
omit Q in
lemma drip_title (hp:4*z≤P_)(g:z≤1)(u:V.funds.direct≤h)(cL:0≤D)(h':0≤V.beta)(Θ:Ward V)(hSigma:Real.exp (-(N_).val^4 * c':ℝ) ≤ Kea.angel m P V.J.M):
    lowerBook N_ z X_ c' ≤ drip V P ∧ 0< drip V P:=by
  have hu:= shell_angle Θ Y' i_.le hp u h' cL; have hv:= lowerBook_pos X_ c' i_ g N_
  have hE:= mul_le_mul hu hSigma (Real.exp_pos _).le (show 0≤Graph.angle V from le_trans (mul_nonneg (pow_nonneg (measureReal_nonneg) _) (Real.exp_pos _).le) hu); exact ⟨hE,hv.trans_le hE⟩
include w_ vL W H a_ h_ p_ f_ t_ e_
lemma dampened_book (T:Real) (T':(∫ x:SU.E,saltWeight group z kL x∂group.probHaar)≤ T*Xμ)
    (g:n≤ (N_).val)(k':0≤k)(t:0≤vA)(c:0≤C)(hy:0≤y)(f:∀ T∈Lace V, Gall.Yep k (mateK (mid m B)) (changeM (m:=m) P T.1 V.J.M) (y*Kea.angel m P V.J.M))(f':∀ T∈Lace V,∀ i:LeanV (Single (mid m B)),Pays k (drawT (spar j V.J.M T.1) i) R)(b:∀ T∈Lace V,HelpP T.1 vA r)(l':pittance (mid m B) vA C≤1)(O:Opt (α:=α) (mid m B))(hp:‖gain O.R‖ ≤ (mid m B).val^2): let z':= baton (mid m B) u vA C k
    phM V O P S ≤ drip V P*(z'*y*feeP O k)+ lite O * upperBook N_ z T (Z_):=by
  intro x; let z':=x -- syntax
  let A:=Kea.angel m P V.J.M; let I:= lite O*Real.exp (Z_); have hI:0≤I:=by unfold I lite; positivity
  let x0:= z'*(y*A)*feeP O k; let F:=fun i:Orbit N_=> recW O P V S i-baseW O P V S i; let B_(i:Orbit N_):= I*diminish z kL i.1
  have he(i:Orbit N_): ‖F i‖ ≤ dim V i*x0+B_ i:=by by_cases ht:i∈Lace V; exact le_trans (pall_b V S Q H i O g ht W (b _ ht) t a_ (zero_le_one.trans h_) k' c hp (f _ ht) hy (f' _ ht) l') (le_add_of_nonneg_right (mul_nonneg hI (dim_eye ..))); rw [Graph.dim, Set.indicator_of_notMem ht,zero_mul,zero_add]; exact road_ext V S Q H W Y' a_ h_ i_ e_ f_ p_ t_ w_ vL g O hp i ht -- g implicit tune
  have hx:= bonB W Y'; obtain ⟨p,q⟩:= integrable_s V S Q H hx O g; let μ:=city N_; have hA:= ((worth hx).integrable μ).mul_const x0; let M:=dim_integral (N:=N_) z kL _ T'; have hb: Integrable B_ μ:= M.1.const_mul _; apply le_trans (integral_mono (p.sub q|>.norm) (hA.add hb) he); unfold μ at *; simp_rw [Pi.add_apply]; rw [integral_add hA hb, integral_mul_const]; unfold B_; rw [integral_const_mul]; refine le_trans (add_le_add_right (mul_le_mul_of_nonneg_left M.2 hI) _) ?_; unfold x0 I upperBook z' A drip angle; apply le_of_eq; ring
end YM.CF.Fixed.Extensive
