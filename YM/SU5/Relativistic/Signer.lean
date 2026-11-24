import YM.SU5.Relativistic.Railcar
import YM.SU5.Relativistic.Sash
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}
    (D : Exhibition Y H a b I E L B)
local notation "V"=>D.univ_
variable (G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (u:ℕ→ℕ) {T:ℕ→Bool→Family (tent Y H)→Family (tent Y H)}(t:GradesAll (i:=a) (a:=G.rows) (k:=b) (b:=G.columns) Y H u T)
variable (d j:Axis) (c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
variable (x:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ)
local notation "χ" i:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) x i (c i)
local notation "ψ"=>evaluate Y H D.univ_ G d c (SameCharacter.resident Y H D.univ_ G d false (c d) x)
local notation "D₀"=> Dome (tent Y H)
local notation "Ξ"=> Cloud (Dome (tent Y H))
local notation "φ" n:max => response Y H V n G.history G.clipped j false (c j) (χ j)
local notation "P" s:max F:max=>stream Y H (fun s=>T s true) s F
local notation "Q"=> G.history
variable (s:ℕ)
local notation "α" => walkV Y H j
local notation "F₀"=> Cabin (tent Y H) j
local notation "κ" u:max=>mirror K j u
local notation "Λ₀"=> Λ.R.L.val
local notation "B₁" s:max=> creed Y H D G d j c x s

open HostLegal MeshClock
local notation "R₁"=> timeMesh Λ
local notation "U"=>flier Y H D G u t d j c x
local notation "W₀" s:max=> Tower.Field Y H s j 0 false
local notation "Ωe"=> doorstep Y H V Q G.clipped j false (c j) (χ j)
local notation "Φ" s:max=> arriving Y H V s Q G.clipped j false (c j) (χ j)
local notation "Υ" s:max=> (U).entry s
local notation "E₁"=> indoor Y H V Q G.clipped j false (c j) (χ j)
local notation "E₂"=> (U).booth
local notation "Δ₀"=> relocate (tent Y H)
local notation "B₀"=> ruler Λ.block
-- for tariffs: geometry under transverse moves. at m high anchor. Economical real translation s. 
local notation "C₂"=> Vacancy.chart
lemma tour_test{Z:Calibration}{p: Finset Cover}{v:Bool}{F:Family Z}(i:Cover)(l:List Axis)(a:InTest Z true p v F): InTest Z true (drivePlot i Z l p) v (cad Z l i F):=by
 induction l with| nil=> exact a| cons i l ih=>exact froll i ih _
lemma passable {P':Finset Cover}{a b:ℤ}(p:Between K j a b P')(i:Cover)(h:i j=0):Between K j a b (streetBox K i P'):=by
 intro q u; obtain ⟨v,t,hv⟩:= Tower.Selected.plots_shifted Y H i q u j; rw [hv,h,mul_zero,add_zero]; exact p v t
local notation "Ms" n:max z:max=> notch (timeMesh Λ) n z
-- purchases relative chart op. time slabs dep relative movers.
variable (T₁: ℕ→ℤ→Family (tent Y H)) (A T':ℝ → ℝ) (W: Slab (timeMesh Λ))
structure TimedOdd (X:E₁→L[ℂ] E₂)(Z:E₂ →L[ℂ] E₁): Prop where
 learns {n:ℕ} (h:s≤n)(p:ℤ) : let y₀:=(Ms n p).val; ∃ (a b:ℤ)(S:Finset Cover),InTest K true S true (T₁ n p) ∧ A y₀= (Ms n a).val∧ T' y₀=(Ms n b).val∧ Sheaf Y H D G u t d j c x (s:=n) (T₁ n p) a b X ∧ Shale Y H D G u t d j c x (s:=n) (T₁ n p) a b Z -- shadow u
-- allow only forward chain Tag multiplier 0 or 1 per H
variable {F:Family (tent Y H)}{S:Finset Cover}{w:ℕ}(q: Bool)
def shifted (r:ℝ) (x:ℝ):ℝ:= if q then r+x else r
lemma shifty (r:ℝ): Continuous (shifted q r):= by cases q; exact continuous_const; exact continuous_const.add continuous_id

def winTurn (q:Bool)(v:Bool)(F:Family (tent Y H))(n:ℕ)(p:ℤ):Family (tent Y H):= relocate (tent Y H) j (if q then p else 0) (stream Y H (fun s=>T s v) s (n-s) F)
local notation "l★" W:max q:max => shifted q ((W).lower:ℝ)
local notation "u★" W:max q:max => shifted q ((W).upper:ℝ)
local notation "Up" n:max F:max v:max q:max=> winTurn Y H (T:=T) j n q v F -- q order? q var earlier, declarations section order `variable T₁ A... W ... S F ...`
variable {r:ℤ}
include t
lemma win_frame (h:InTest K true S true F)(wP:0<w)(z:Between K j (B₀*r) (B₀*(r+w)) S)(hw:Ms s r=W.lower)(he:Ms s (r+w)=W.upper):∃ X Z, TimedOdd Y H D G u t d j c x s (Up s F true q) (l★ W q) (u★ W q) X Z:=by
 let R:=plow K j (-r) S; let H':= Δ₀ j (-r) F; have hp:Between K j 0 (ruler (tent Y H).B*w) R:=by
    have hg:= z.relocate K j (-r); change Between K j (B₀*(-r)+_) (B₀*(-r)+_) _ at hg
    rw [show B₀ *(-r)+ B₀*r=0 by ring,show B₀*(-r)+B₀*(r+w)=B₀*w by ring] at hg; exact hg
 let B': Slice K j w:= ⟨H',R,froll j h _,hp⟩
 refine ⟨blossoms Y H D G u t d j c x s B' wP,otters Y H D G u t d j c x s B' wP,⟨?_⟩⟩
 intro n h₀ p y'
 let X':=Λ₀^(n-s); let B₀':=uphill Y H D G u t j s B' h₀; let r':=castor R₁ s n r; let z':=if q then p else 0; let a:=r'+z'
 have g0:(Ms n r')=W.lower:= (notch_up R₁ s n h₀ r).trans hw
 have g1:(Ms n (r'+((X'*w:ℕ):ℤ)))=W.upper:= by
    rw [←he,←notch_up R₁ s n h₀]; unfold r' X' castor; rw [mul_add]; push_cast; rfl
 let gA:=winTurn (T:=T) Y H j s q true F n p
 have hr: (B₀').f= Δ₀ j (-a) gA:=by
    change (P s (n-s)) (Δ₀ j (-r) F)= Δ₀ j _ (Δ₀ j z' ((P s (n-s)) F))
    rw [grade_ho Y H D G u t j s h, edge_roll j _ _ (t.allSupport Y H V Q _ s _ h),mul_neg]
    have hx: -a+z'= -r':=by unfold a; abel
    rw [hx]; rfl
 have h0(r':ℤ)(b:Stamp R₁)(t:Ms n r'=b): shifted q b.val y'= (Ms n (r'+z')).val:=by
    rw [notch_add,AddSubgroup.coe_add,t]; unfold z'; cases q <;> simp only [shifted,Bool.false_eq_true,ite_false,ite_true,notch_zero,AddSubgroup.coe_zero,add_zero] <;> rfl
 refine ⟨a,a+(X'*w:ℕ),_,froll j (t.allSupport Y H V Q u s (n-s) h) z',h0 _ _ g0,?_,?_,?_⟩
 · unfold a; rw [add_right_comm]; exact h0 _ _ g1
 · rw [petals Y H D G u t d j c x s B' wP h₀]; exact sheaf_h Y H D G u t d j c x n _ _ rfl hr
 rw [back_petals Y H D G u t d j c x s B' wP h₀]; exact shale_h Y H D G u t d j c x n _ _ rfl hr
-- even analog
structure TimedEve (X:(E₁).Op): Prop where
 learns {n:ℕ}(h:s≤n)(p:ℤ): let z:=(Ms n p).val; ∃ a b:ℤ,TestFamily K true (T₁ n p) ∧ A z=(Ms n a).val∧ T' z=(Ms n b).val ∧ Glair Y H D G d j c x (s:=n) (T₁ n p) a b X
lemma dawn_frame (h:InTest K true S false F)(wP:0<w)(z:Between K j (B₀*r) (B₀*(r+w)) S)(hw:Ms s r=W.lower)(he:Ms s (r+w)=W.upper):∃ X, TimedEve Y H D G d j c x s (Up s F false q) (l★ W q) (u★ W q) X:=by
 let R:=plow K j (-r) S; let H':= Δ₀ j (-r) F; let H₁:=froll j h (-r); have hp:Between K j 0 (ruler (tent Y H).B*w) R:=by
    have hg:= z.relocate K j (-r); change Between K j (B₀*(-r)+_) (B₀*(-r)+_) _ at hg
    rw [show B₀*(-r)+B₀*r=0 by ring,show B₀*(-r)+B₀*(r+w)= B₀*w by ring] at hg; exact hg
 let u':W₀ s:= ⟨H',(purpose_ok ..).mpr ⟨⟨R,H₁,by rw [area0]; exact fun i a=>(hp i a).1⟩,nofun⟩⟩; let B':Entry Y H s j false w:=⟨u',R,H₁,hp⟩
 let C:=entrance Y H V s Q G.clipped j false (c j) B' wP
 refine ⟨procession Y H V Q G.clipped j false (c j) (χ j) C,⟨?_⟩⟩
 intro n h₀ p y'; let X':=Λ₀^(n-s); let J:=furnished Y H s Q j false w B' n h₀; let r':=castor R₁ s n r; let z':=if q then p else 0; let a:=r'+z'
 have g0:(Ms n r')=W.lower:= (notch_up R₁ s n h₀ r).trans hw; -- semicolon
 have g1:(Ms n (r'+((X'*w:ℕ):ℤ)))=W.upper:=by rw [←he,←notch_up R₁ s n h₀]; unfold r' X' castor; rw [mul_add]; push_cast; rfl
 let P':=stream Y H (fun s=>T s false) s (n-s); let gA:=winTurn (T:=T) Y H j s q false F n p
 have hr:J.val.val= Δ₀ j (-a) gA:=by
    change stream Y H G.refine s (n-s) (Δ₀ j (-r) F)= Δ₀ j _ (Δ₀ j z' (P' F))
    rw [← t.originally Y H V Q u s (n-s) (aux_test H₁), grade_ho Y H D G u t j s h, edge_roll j _ _ (t.allSupport Y H V Q _ s _ h),mul_neg]
    have hx: -a+z'= -r':=by unfold a; abel
    rw [hx]; rfl
 have h0(r':ℤ)(b:Stamp R₁)(t:Ms n r'=b): shifted q b.val y'= (Ms n (r'+z')).val:=by
    rw [notch_add,AddSubgroup.coe_add,t]; unfold z'; cases q <;> simp only [shifted,Bool.false_eq_true,ite_false,ite_true,notch_zero,AddSubgroup.coe_zero,add_zero] <;> rfl
 refine ⟨a,a+(X'*w:ℕ),aux_test (froll j (t.allSupport Y H V Q u s (n-s) h) z'),h0 _ _ g0,?_,?_⟩
 · unfold a; rw [add_right_comm]; exact h0 _ _ g1
 let g:0 < X'*w:=Nat.mul_pos (pow_pos Λ.R.L.property _) wP
 rw [show C=entrance Y H V n Q G.clipped j false (c j) J g from Subtype.ext (refined_box Y H V s Q G.clipped j false (c j) w B' wP n h₀)]
 exact glair_h Y H D G d j c x n g J rfl hr
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.win_frame
