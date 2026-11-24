import YM.CF.Dial.Say
/-! Pair of endpoints, preconditions for unsquared lift. -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
section mat
variable {n:Type*}[Fintype n][LinearOrder n][Nonempty n] {P C:Op n}
lemma stage_idem (h:IsStarProjection P): stage P (victory P C C P)=stage P C:=by
  have hp: P*C*Pᵀ=body P C:=by rw [body,cc,h.isSelfAdjoint.star_eq]
  rw [victory,hp,← show stage P C= _ from rfl]; change stage P (stage P C)=stage P C
  have he: body P (stage P C)=body P C:=by rw [body, stage_left h,body_right h]
  have ht: stage (1-P) C=stage P C:=by rw [stage,stage,sub_sub_cancel,add_comm]
  rw [stage,he, ← ht]; have hh:body (1-P) (stage (1-P) C)=body (1-P) C:=by nth_rw 1 [body]; rw [stage_left h.one_sub,body_right h.one_sub]
  rw [hh,ht]; rfl
lemma stage_here(h:IsStarProjection P)(C: Op n)(a:ℝ): stage P (straightC P C C P a)=stage P C:=by rw [straightC,stage_p,stage_idem h,← add_smul]; simp
lemma nothing_z(h:IsStarProjection P)(p:IsUnit (stage P C))(m t:ℕ):rockZ (straightC P C C P) P t m=0:=by
  have hc(x y:ℝ): relay P (straightC P C C P x) (straightC P C C P y)=1:=by
    rw [relay,←stage_left h, stage_here h,stage_here h,stage_left h]; exact relay_base h p
  apply Finset.sum_eq_zero; intro i _; simp [spark,hc,Fock.invoice,Fock.slope]
end mat
variable {N:Side}
def couple (U:Bkg (More N))(x y:Stun N): Sew N N:=((U,U),y,x) -- order
structure Gaze (U:Bkg (More N))(x y:Stun N)(e:ℝ): Prop where
 gift:Cube.Guard U e
 hi: Slow U (hook x) e
 lo: Slow U (hook y) e
 close i: ‖hook x i-hook y i‖<e
lemma Gaze.glimp(U:Bkg (More N))(x y:Stun N){e:ℝ}(g:Gaze U x y e)(h:0<e): Gild (idrat N) (couple U x y) e:=by
  refine ⟨jointly U g.gift h,g.lo,g.hi,fun i=>?_⟩
  rw [filed,norm_sub_rev]; exact g.close i
lemma Gaze.wider{U:Bkg (More N)}{x y:Stun N}{e d:ℝ}(h:Gaze U x y e)(p:e≤d): Gaze U x y d:= ⟨h.gift.shrink p,fun i a=>(h.hi i a).trans_le p,fun i a=>(h.lo i a).trans_le p,fun i=>(h.close i).trans_le p⟩
variable (j m:ℕ)
def openC (M:Male)(U:Bkg (More N))(x y:Stun N):ℂ:=Matrix.trace (earnings (repeated j) (repeated j) m M (idrat N) (post (couple U x y)))
def spar (j:ℕ)(M:Male)(U:Bkg (More N)):Op (Single N):= funde j M _ (profile U)
def coneP(M:Male)(U:Bkg (More N))(x:Stun N): Wave (Single N):= filled (spar j M U) (postC x)
abbrev PairsB (j m:ℕ)(e:ℝ)(N:Side)(M:Male) := ∀(U:Bkg (More N))(x y:Stun N), Gaze U x y e→ IsStarProjection (spar j M U) ∧ Complex.exp (openC j m M U x y) • coneP j M U x=coneP j M U y ∧ coneP j M U x≠0 ∧ (x=y→ openC j m M U x y=0)
def blendS (j m:ℕ)(c K a:ℝ)(t:ℕ) :=IndexB 1 (false,true) (false,true) (earnings (repeated j) (repeated j) m) a K c t
lemma stops(hj:1≤j)(p:0<m)(h:Joy 1 (repeated j) (repeated j) m): ∃ e a K:ℝ,0<e∧0<a∧0<K∧∃ t:ℕ,blendS j m e K a t∧ ∀{N:Side}, t≤N.val→∀ i:Male, PairsB j m e N i :=by
  let ho : Odd (1:Side).val:=odd_one
  let Q:=monoto j hj
  obtain ⟨a,K,b,S,T,U,v,H⟩:= Q.stable ho p h
  obtain ⟨d,g,l,V⟩:= (((Q.taxes ho p h).plus (festival j hj 1)).plus h)
  refine ⟨min b d,a,K,lt_min U g,S,T,max v l, fun i N P G he hv=> (neck (lt_min U g) (min_le_left b d) H) i G he ((le_max_left ..).trans hv),?_⟩
  intro N hl M x i y hp
  let G:=idrat N; let z:= couple x i y
  obtain ⟨⟨hX,hZ⟩,W⟩:= V G rfl ((le_max_right ..).trans hl) z ((hp.wider (min_le_right ..)).glimp _ _ _ g)
  have hs:=match_ci j hj z M (hZ M).1 (hX M)
  refine ⟨(hZ M).1, hs.1, hs.2.1, fun u=> ?_⟩
  let P:=repeated j M G (post z); let A:=squareD G true (post z); let B:=squareD G false (post z)
  have he: IsStarProjection P:= carts_p (switchG G).symm (hZ M).1
  have hc:B=A:=by rw [show B=_ from chord_same _, show A=_ from square_true ..]; rw [show z.2.1= z.2.2 from u.symm]
  have hh: tonic (repeated j) (repeated j) M G (post z)=straightC P A A P:=by rw [tonic]; change straightC P A B P=_; rw [hc]
  have hw:= (W M (termJ m 0)).1; rw [hh,stage_here he] at hw
  change (earnings (repeated j) (repeated j) _ _ _ _).trace=0; change (earnings _ _ m M G (post z)).trace=0;
  rw [show (earnings _ _ _ M G (post z)).trace=_ from (hX M).1, hh]; exact nothing_z he hw _ _
end YM.CF.Dial
