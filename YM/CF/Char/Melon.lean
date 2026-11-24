import YM.CF.Char.Bois
set_option autoImplicit false
noncomputable section
namespace YM.CF.Char
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
open Push Push.Uniform
local notation "Y₀"=> bareStores S
local notation "uΠ"=> pageX (G:=G) F x
local notation "Z₀"=> clipped T x F k
variable {u:Mast G c}{a:Fish (Key F G)}
lemma axed(q:Chi)(b:ℝ){K:Teller G}(Y:LinkArray G (Frozen Y₀ x F))(Q: Teller.Funds K S T)(h: ∀ i, i<l → ContDiffAt ℝ ω Z₀ (meetVar u (Newt.sol S T k x F i u))) :
 orbitP T x (facadeX G u) k Y₀ F q b Y l=leaveX F x (Newt.sol S T k x F l u):=by
 let V:= facadeX G u; have hp:facadeX G u=AnalyticBridge.SectorAffine.field 1 (reader G c (hull G c u)):= (reader_field ..).symm
 induction l with
 | zero => rw [orbitP,hp]; unfold Newt.sol; rw [streak,budX,visit_right]; exact (Heir.school_eq Q F x k q b Y _).symm
 | succ i ih =>
    let m:=Newt.sol S T k x F i; let φ:=Slope Z₀ (meetVar u (m u)); let A:= pushed T x V k Y₀ F (leaveX F x (m u)); let L:=columnX T x V k Y₀ F
    have he: A=leaveX F x φ:= by rw [show φ=visitX F x A from funext fun j=> (driveB j (h _ (by omega))).symm,visit_right]
    rw [orbitP, ih (fun i hi=>h i (by omega)), swingP]; change _-(L.transpose *ᵥ A)=leaveX F x (Newt.sol S T k x F (i+1) u); rw [he]; unfold Newt.sol; rw [streak,nudge,one_smul]; change _=leaveX F x (m u-gall T x k F u φ)
    rw [map_sub,show gall T x k F u=paintO ((L.transpose).submatrix uΠ uΠ) from ?_, tableVisit]
    · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,visit_right]; rfl
    unfold gall L columnX panelPi V; simp only [hp,zero_smul,add_zero]
-- clip Scatter, analytic uniform with slack
abbrev peak(n:ℕ)(P:Patch)(K:Teller G):=Newt.tailP P K.top.width n
lemma tip_left (n j:ℕ)(P:Patch)(K:Teller G):0<peak n P K ∧∀ᶠ x:ℝ in atTop, ∀{c f:Side}(S:StepData c f)(T:Tube G S), Cert P K S T x  → ∀ (F:Forest S.ratio)(k:S.Choices)(u:Positions (Joint F G)), ‖u‖<1 → 
 Wax (costP F k T.high T.up-clipped T x F k) u n (peak n P K) (temp x^j):=by
 obtain ⟨v,hv⟩:= Uniform.paint_supply G n; have he:=Uniform.width_positive (half_pos K.top.width_pos) n P.L
 refine ⟨div_pos he (by positivity),?_⟩ -- tune
 let U:=muskP G n v K.top.width K.top.paths P.L
 filter_upwards [smallF (n:=j) (half_pos K.top.width_pos) |U|] with x hx c f S T Q F k u hU
 have hp:=Q.funds.1; obtain ⟨a,b,hL,hJ⟩:=hp.feeds; rw [←hp.high] at hL
 have hh:=tail_paid hL (Stores.till x) F k hv u (mem_ball_zero_iff.mpr hU); rw [Q.got] at hh; exact hh.mono ((mul_le_mul_of_nonneg_left (le_abs_self U) (Real.exp_pos _).le).trans hx)
variable {P:Patch}{K:Teller G}{n i:ℕ}{r' D ε C a' d' t X s:ℝ}
def sizedP(G:Gauge)(P:Patch)(K:Teller G)(S:StepData c f)(T:Tube G S)(F: Forest S.ratio):Prop:=∃ z, Critical F T.high T.up z ∧ Guessed F (Bloch.installed S.ratio T.R.A0) z
structure chosen (n:ℕ)(F:Forest S.ratio)(T:Tube G S)(x s A:ℝ)(i:ℕ):Prop where
 -- on the whole normalized ball
 root (k:S.Choices) (y:Mast G c) :‖y‖ < 1 →  Jet.Allows n (fun u=>Newt.sol S T k x F i (s • u)) y (A*s)
lemma sized (n i:ℕ)(ht:2 ≤ n)(P:Patch)(K:Teller G)(B:P.Branches K.bind G)(W:Before G K.top.width K.top.paths K.j K.bind (n+1+1)) :
 ∃ A ε:ℝ, 0<A∧0<ε∧ ∀ᶠ x:ℝ in atTop, ∀ {c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x →  sizedP G P K S T F → ∀ s,0<s → temp x  ≤  s  →  s ≤ ε →  chosen n F T x s A i:=by
 obtain ⟨a,t,v,C,r,ha,ht',hv,hC,hR,h⟩ := yields K n i ht P B W
 refine ⟨t+C,min r (min 1 (a/2)),add_pos ht' hC, lt_min hR (lt_min zero_lt_one (half_pos ha)),?_⟩
 filter_upwards [h] with x hx c f S T F Q hc s hs hp hS
 obtain ⟨z,hz,h₁,h₂,h₃⟩:= hx S T F Q hc
 have ht'':=hS.trans (min_le_left ..); have he :s<a:= (hS.trans ((min_le_right ..).trans (min_le_right ..))).trans_lt (half_lt_self ha); have hy:s ≤ 1:=hS.trans ((min_le_right ..).trans (min_le_left ..))
 have hg: station z 0=0:=by simp [station,hz.critical.1]
 refine ⟨fun k y hY=>?_⟩
 have hX:=near_s (r:=a) (f:=station z) hs.le hy (by omega : 1 ≤ n) he (fun y hy=>(h₁ y hy.le).2.1) hY.le; rw [hg] at hX; simp_rw [sub_zero] at hX
 have hZ: s^(i+2) ≤ s:= (pow_le_pow_of_le_one hs.le hy (show 1 ≤ i+2 by omega)).trans_eq (pow_one _)
 have hq:=(((h₃ k s hs hp ht'').due y hY).mono (mul_le_mul_of_nonneg_left hZ ht'.le)).add hX
 apply (hq.mono (add_mul t C s).ge).germ; exact Eventually.of_forall fun z=>sub_add_cancel ..
lemma chosen.mono (h:chosen n F T x s X i)(ht:0 ≤ s)(hp:X ≤  t):chosen n F T x s t i:=⟨fun k v hv=> (h.root k v hv).mono (mul_le_mul_of_nonneg_right hp ht)⟩
lemma sized_all (n:ℕ)(ht:2 ≤ n)(P:Patch)(K:Teller G)(B:P.Branches K.bind G)(W:Before G K.top.width K.top.paths K.j K.bind (n+1+1))(i:ℕ) :
 ∃ A ε:ℝ, 1 ≤ A∧0<ε∧ ∀ᶠ x:ℝ in atTop, ∀ {c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x →  sizedP G P K S T F → ∀ s,0<s → temp x  ≤  s  →  s ≤ ε →  ∀ j ≤ i,chosen n F T x s A j:=by
 induction i with
 | zero => obtain ⟨A,v,hA,hv,h⟩:=sized n 0 ht P K B W; refine ⟨max A 1, v,le_max_right .., hv,?_⟩; filter_upwards [h] with x hx c f S T F h u s he hp hv i h'; have ht:=hx S T F h u s he hp hv; rw [show i=0 by omega]; exact ht.mono he.le (le_max_left ..)
 | succ i ih =>
    obtain ⟨A,v,hA,hv,h⟩:=sized n (i+1) ht P K B W; obtain ⟨D,M,hD,hM,hZ⟩:=ih; refine ⟨max A D,min v M,hD.trans (le_max_right ..), lt_min hv hM,?_⟩
    filter_upwards [h,hZ] with x hx he c f S T F H hc s hs hT hS i' h'
    by_cases i' ≤ i
    next hp => exact (he S T F H hc s hs hT (hS.trans (min_le_right ..)) _ hp).mono hs.le (le_max_right ..)
    rw [show i'=i+1 by omega]; exact (hx _ _ F H hc s hs hT (hS.trans (min_le_left ..))).mono hs.le (le_max_left ..)
lemma chosen.lands(h:chosen n F T x s C i)(ht:0<s)(hp:1 ≤  C)(hu:‖u‖<1)(hT:C*s < r') : ‖meetVar (s•u) (Newt.sol S T k x F i (s•u))‖ < r':=by
 rw [norm_meet]; apply max_lt
 · rw [norm_smul, Real.norm_eq_abs,abs_of_pos ht]; exact ((mul_le_of_le_one_right ht.le hu.le).trans (le_mul_of_one_le_left ht.le hp)).trans_lt hT
 exact (h.root k u hu).value.trans_lt hT
lemma cup (n i:ℕ)(ht:2 ≤ n)(P:Patch)(K:Teller G)(B:P.Branches K.bind G)(W:Before G K.top.width K.top.paths K.j K.bind (n+1+1)):
 ∃ A ε:ℝ,1  ≤  A∧0<ε∧∀ᶠ x:ℝ in atTop, ∀{c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x  →  sizedP G P K S T F  →  ∀ s,0<s → temp x ≤ s → s ≤ ε → ∀ j ≤ i,chosen n F T x s A j∧∀(q:Chi)(d:ℝ)(Y:LinkArray G (Frozen (bareStores S) x F))(k:S.Choices)(u:Mast G c), ‖u‖<1 →  let C:= orbitP T x (facadeX G (s•u)) k (bareStores S) F q d Y j; let v:=Newt.sol S T k x F j (s•u)
 C=leaveX F x v ∧(headed T x (facadeX G (s•u)) k (bareStores S) F C).submatrix (pageX F x) (pageX F x)=Uniform.block (clipped T x F k) (meetVar (s•u) v):=by
 obtain ⟨D,d,C,hD,hd,hC,h⟩:= Newt.mat_paid K P _ (by omega) W
 obtain ⟨A,X,hA,hX,hp⟩:= sized_all n ht P K B W i
 let R:=min D 1; have hR:0<R:=lt_min hD zero_lt_one; have hB:0<A:=zero_lt_one.trans_le hA
 refine ⟨A,min X ((R/2)/A),hA,lt_min hX (by positivity),?_⟩
 filter_upwards [hp,(tip_left (n+1+1) 1 P K).2, PatchReads.reserve K P, Work.E01.radiusB_tendsto.eventually_ge_atTop 1000] with x hx he hp' hl c f S T F hT hv s hs hS hY
 have hE:= hx S T F hT hv s hs hS (hY.trans (min_le_left ..)); have hh:A*s < R:= ((mul_comm ..).trans_le ((le_div_iff₀ hB).1 (hY.trans (min_le_right ..)))).trans_lt (half_lt_self hR)
 have hC (j)(k:S.Choices)(u:Mast G c)(hj:j ≤ i)(hu:‖u‖<1) : ContDiffAt ℝ ω (clipped T x F k) (meetVar (s•u) (Newt.sol S T k x F j (s•u))):=by
    let f:=costP F k T.high T.up; have hZ := chosen.lands (k:=k) (hE j hj) hs hA hu hh
    nth_rw 1 [← sub_sub_cancel f (clipped T x F k)]; exact (((h S T x hT).2.2.2 F k).2 _ (hZ.trans_le (min_le_left ..))).1.sub (he S T hT F k _ (hZ.trans_le (min_le_right ..))).1
 intro j hj; refine ⟨hE j hj,?_⟩
 intro q d Y k u hu C v
 have hπ : C=leaveX F x v:= axed q d Y hT.funds.1 (fun i h=> hC i k u (h.le.trans hj) hu)
 refine ⟨hπ,?_⟩; rw [hπ]; exact heart_all (hp' S T hT.got hT.size hT.funds.1) (hC _ k u hj hu) hl
end YM.CF.Char
