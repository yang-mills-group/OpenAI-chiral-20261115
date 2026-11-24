import YM.SU5.Macro.Ascents
import YM.SU5.Macro.Spot
/-! # What split readings the paid pair rules out

Even enough to test the comparator on **separately Cell-registered** inputs. Namely
read one mixed product of a gauge×matter monomial at the early cell times a gauge×matter
monomial at the late cell. Predict by the cost of the two gauges (JOINTLY in those two
same locations) times cost of the two Row matter parts (JOINTLY in those very two locations).
This doesn't hypothesize factorization *between the cells*. Does take pure charged-even
marginals in the qualification from the given same law. See also `Comparison.ofSinglet`
for the variant formulating even those test prices using only gauge-INVARIANT probes.
-/
set_option autoImplicit false
set_option maxHeartbeats 470000
set_option maxRecDepth 4500
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selection.Home
open Function Filter NormedSpace Metric SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude
open Tower.PhaseChoice Tower.Selected Tower.Reconstruction
open CF.SatinRotation CF.Pannier.Chancel.Attic.Cairn Buffered.Reliance Buffered.Reliance.ShortWave
open CF.Pannier.Chancel CF.Pannier.Chancel.Lantern CF.Pannier.Chancel.Lantern.Bulb
open Rubric Fern Fern.Planet
open OS.Semigroup MeshClock
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    {L: Rack Λ l} {B:Clay Λ l} {T:ℕ→ℕ→Tariff} {t:ℕ→Tariff} (D: Fashion Y H i k I E L B T t)
    (G:SatinVerification.GroundExtension (i:=i) (k:=k) (E:=E) Y H) (room : ∀ j:Axis,Arena Y H G.history.circuit j 0 false)
    (χ:CapCharacter Y H D.univ_ G.history G.clipped 3 false (room 3))
local notation "V" => D.univ_
local notation "Q" => G.history
local notation "Qt" => G.clipped
namespace Siam
open Giant
variable (s:ℕ) (M:Giant)
local notation "Φ" => Torrent.fare
local notation "A" => early M
local notation "S" => M.ascX
local notation "Wz" => wall M
local notation "Mρ" z:max u:max a:max b:max c:max => Rubric.Marble K z M.Zumba M.ascX M.ascY u a b c
local notation "k₀" f:max => phaseRead Y H V Q Qt 3 (room 3) χ s f
open Monochrome
namespace Comparison
local notation "Γ" => sch Y H D G room (dial Y H D G room 3 χ 0)
local notation "Ξ" => Dome (tent Y H)
abbrev Area:= early M ∪ M.ascX
local notation "P" => Area M
local notation "⚑" => Bay K (P)
local notation "φ" => pinhole (Dome (tent Y H)) s
local notation "δ" => Torrent.fare
variable (W:Window.Family)

section board
variable (J:Calibration) (X:Finset Cover)
abbrev assign {x:Family J}(h:InTest J true X false x): Bay J X:= ⟨⟨x,broadCompile J X h⟩,h⟩
-- names Young etc
noncomputable def castL (p:ℕ)(q r:ℕ)(h:cameo p q=false) : Marble J W M.Zumba M.ascX M.ascY X p q r→ₗ[ℂ] Bay J X where
 toFun x:= assign J X (h ▸ ((Marble.assign x.property).widen))
 map_add' _ _:=rfl
 map_smul' _ _:=rfl

local notation "Rr" X:max p:max q:max r:max => Rubric.Row J W M.Zumba M.ascX M.ascY X p q r
local notation "xR" p:max q:max r:max => Marble J W M.Zumba M.ascX M.ascY X p q r
lemma linear_zero (p q r:ℕ)(w:xR p q r→ₗ[ℂ] ℂ) (h:∀ (F: xR p q r) (x:Family J) (g: PairsC→ℂ),
    (Rr X p q r) x → Coeff false X g → F.val=scalar J g*x → w F=0): w=0 := by
   apply (Submodule.linearMap_eq_zero_iff_of_eq_span w («S»:= {f|∃ (g:PairsC→ℂ) (x:Family J), Coeff false X g ∧ (Rr X p q r) x ∧ f=scalar J g*x}) rfl).mpr
   rintro ⟨g,x,y,w,v,e⟩; exact h _ y x v w e
end board

-- price rule at this stance: inclusions preserve Family/side and gauge location.
def packBefore : Bay K (early M) →ₐ[ℂ] ⚑ := Subalgebra.inclusion (show Bay K (early M) ≤ Bay K (P) from tallerBay K _ true Finset.subset_union_left)
def packAfter : Bay K M.ascX →ₐ[ℂ] ⚑ := Subalgebra.inclusion (show Bay K M.ascX ≤ Bay K (P) from tallerBay K _ true Finset.subset_union_right)
local notation "iL" => packBefore Y H M
local notation "iR" => packAfter Y H M
local notation "Σ" p:max q:max => iL p * iR q
local notation "tA"=> Bay K A
local notation "tB"=> Bay K S
local notation "Kx" x:max => (x).val.val
local notation "R_" p:max q:max r:max s:max g:max => Rubric.Row K W M.Zumba M.ascX M.ascY p q r s g
local notation "M₀" i:max => R_ (early M) 0 10 0 (Kx i)
local notation "M₁" i:max => R_ M.ascX 10 0 1 (Kx i)
/-- Local gauge-only Cost-generator qualification. Not saying Gauge singular or
    gauge-SINGLET (we are in the wider ambient system). -/
def JustGauge (J:Calibration)(B:Finset Cover)(x:Bay J B): Prop:= ∃ g:PairsC→ℂ, Coeff false B g∧ x.val.val=scalar J g
/-- Registration rule, imposing factor prediction on the two actual separated cells.
Defined within the one-slot ambient even chart of the union world, so facts also
apply to e.g. global linear predictions on Cloud, composing with that pinhole
(see `Cloud_price` below). `w` is comparison publisher. `t` is reader to take the separate
marginals from. -/
def rule (w: Bay K (Area M) →ₗ[ℂ] ℂ)(t: Bay K (Area M)→ℂ): Prop :=
   ∀ (a g: tA) (b f:tB), JustGauge K A a → JustGauge K S b →
     M₀ g→ M₁ f→ w (Σ (a*g) (b*f))=t (Σ a b)*t (Σ g f)
-- λ price extraction on one position
local notation "R₀" => Mρ W A 0 10 0
local notation "R₁" => Mρ W M.ascX 10 0 1
local notation "upL" => castL M W K A 0 10 0 (show cameo 0 10=false from by decide)
local notation "upR" => castL M W K S 10 0 1 (show cameo 10 0=false from by decide)
private lemma killsB (w: ⚑ →ₗ[ℂ] ℂ) (b:tA)
    (e:∀ (a f:tB), JustGauge K S a→ M₁ f→ w (Σ b (a*f))=0) (s:R₁) : w (Σ b (upR s))=0:=by
   let t:= w.comp ((LinearMap.mulLeft ℂ (iL b)).comp ((iR).toLinearMap.comp (upR)))
   have ht:t=0:=by
      apply linear_zero M W K S 10 0 1 t; intro F x g y z p
      let b':tB:= assign K M.ascX ((InTest.seed z).widen); let x':tB:= assign K M.ascX ((show cameo 10 0=false from by decide) ▸ (Rubric.Row.assign y).widen)
      have he: (upR) F=b'*x':= Subtype.ext (Subtype.ext p)
      exact (congrArg (fun x=> w (iL b* iR x)) he).trans (e b' x' ⟨g,z,rfl⟩ y)
   exact DFunLike.congr_fun ht s
private lemma kills (w: ⚑ →ₗ[ℂ] ℂ)
    (e:∀ (a g:tA)(b f:tB), JustGauge K A a → JustGauge K S b → M₀ g → M₁ f → w (Σ (a*g) (b*f))=0)
    (x:R₀) (y:R₁) : w (Σ (upL x) (upR y))=0:=by
   let t:= w.comp ((LinearMap.mulRight ℂ (iR (upR y))).comp ((iL).toLinearMap.comp (upL)))
   have ht:t=0:=by
      apply linear_zero M W K A 0 10 0 t; intro F u g d q p
      let a:tA:= assign K A ((InTest.seed q).widen); let u':tA:= assign K A ((show cameo 0 10=false from by decide) ▸ (Rubric.Row.assign d).widen)
      have he: (upL) F=a*u':= Subtype.ext (Subtype.ext p)
      exact (congrArg (fun x=> w (iL x* iR (upR y))) he).trans (killsB Y H M W w (a*u') (fun s x i v=> e a u' s x ⟨g,q,rfl⟩ i d v) y)
   exact DFunLike.congr_fun ht x

def earn : (Bay K (Area M)) →ₗ[ℂ] ℂ := (sch Y H D G room (dial Y H D G room 3 χ 0)).comp
  ((pinhole Ξ s).toLinearMap.comp (Bay K P).val.toLinearMap)
local notation "α" => earn Y H D G room χ s M
lemma earn_at (x: ⚑) : α x=k₀ (Kx x):= sch_hole Y H D G room 3 χ s x.val

/-- The product pure-matter probe is charged (even at this resolution)
    by precisely one unit of this sector under `flash D`. So true price zero. -/
lemma pure_charge_bill (a : tA) (b:tB) (p:M₀ a)(q:M₁ b): α (Σ a b)=0:= by
   rw [earn_at]; exact Rubric.unmixed (phase_unit Y H V Q Qt 3 (room 3) s χ P) (show cameo 10 10=false from by decide) (show ¬5∣(1:ℕ) from by decide) (Rubric.Row.grip (p.wider (T:=Area M) Finset.subset_union_left) (q.wider (T:=Area M) Finset.subset_union_right))
lemma zero_exists : rule Y H M W 0 (α):= fun a g b f _ _ t h=> by
  rw [pure_charge_bill Y H D G room χ s M W g f t h,mul_zero]; rfl

variable {f g:Dome (tent Y H)} {ε:ℝ} (z:Signal Y H D G room χ s M f g W ε)
-- avoid project probate through term using z field; importer uses explicit pair.
local notation "a·" => assign K (early M) ((Signal.left Y H D G room χ s M z).widen)
local notation "b·" => assign K M.ascX ((Signal.right Y H D G room χ s M z).widen)
local notation "π" => Σ (a·) (b·)
include z
lemma failure_pair (w: Bay (tent Y H) (Area M) →ₗ[ℂ] ℂ) (p:rule Y H M W w (α)) :
    w (π)=0 ∧ Φ < ‖α (π)- w (π)‖:=by
  have h:w (π)=0:= kills Y H M W w (fun a c b d u v x y=>
    (p a c b d u v x y).trans (by rw [pure_charge_bill Y H D G room χ s M W c d x y,mul_zero])) ⟨_,z.young⟩ ⟨_,z.aged⟩
  exact ⟨h,by rw [h,sub_zero, earn_at]; exact z.elector⟩

def projected (m:Side)(h:Hosp (Area M) ((tent Y H).c m))(t:Spot (tent Y H) (Area M) →ₗ[ℂ] ℂ) : Prop:=
    rule Y H M W (t.comp (accessor K (Area M) m h)) (fun x:Bay K (Area M)=> earn Y H D G room χ s M (fromSpot K (Area M) (accessor K (Area M) m h x))) -- even readings *in* projected sector.
omit z in
lemma projected_means (m:Side)(h:Hosp P ((K).c m))(x:⚑): α ((fromSpot K P) (accessor K P m h x))=α x:= by
  rw [Monochrome.renew,earn_at,earn_at]; let y:=reGauge K P m h x
  exact (phase_read Y H V Q Qt 3 (room 3) s χ (bidding Y H y.val)).trans ((congrArg χ (settles P m Y H V G 3 (room 3) s h x)).trans (phase_read Y H V Q Qt 3 (room 3) s χ (bidding Y H x.val)).symm)
omit z in
lemma projected_exact (m:Side)(h:Hosp (Area M) ((tent Y H).c m))(t:Spot (tent Y H) (Area M) →ₗ[ℂ] ℂ) :
    projected Y H D G room χ s M W m h t ↔ rule Y H M W (t.comp (accessor K (Area M) m h)) (α):= by
  unfold projected rule; simp_rw [projected_means]
omit z in
lemma projector_exists : ∃ m: Side, ∃ h:Hosp (Area M) ((tent Y H).c m), projected Y H D G room χ s M W m h 0:= by
  obtain ⟨m,h⟩:= (separates K P).exists
  exact ⟨m,⟨h⟩,by rw [projected_exact]; exact zero_exists Y H D G room χ s M W⟩
omit z in
lemma prices_fit (x: Spot K (Area M)) : pinhole Ξ s x.val ∈PolAt Y H s (footprint Λ l s (early M) ∪ footprint Λ l s M.ascX):= by
  have he: x.val∈ bay K P true ∧ x.val∈ enclave K:= x.property
  rw [show _ ∪ _=footprint Λ l s (Area M) from ?_]
  · exact oneSlotWell Λ K l true _ _ s (Set.mem_inter (Set.mem_univ _) (Set.mem_Iic.mpr le_rfl)) (x:=x.val) ((keeps ..).mpr ⟨P,he.1,has_footprint Λ l s P⟩) he.2
  simp only [footprint_eq,silhouette_union,Area]
/-- Auditor can even ask entirely gauge invariant charges with the stated projection step. Same aggregate support. -/
theorem ofSinglet (m:Side)(h:Hosp (Area M) ((tent Y H).c m)) (w:Spot (tent Y H) (Area M) →ₗ[ℂ] ℂ) (p:projected Y H D G room χ s M W m h w) :
    let R:= accessor K P m h (π)
    R.val=f*g ∧ w R=0 ∧ Φ< ‖w R - Γ ((φ f)*(φ g))‖:= by
  intro R
  have he:R.val=f*g:= congrArg (fun x:Bay K P=> x.val) (legacy K P m h π (show f*g∈ enclave K from (enclave ..).mul_mem z.gaugeEarly z.gaugeLate))
  obtain ⟨e,v⟩:= failure_pair Y H D G room χ s M W z _ ((projected_exact Y H D G room χ s M W m h w).1 p)
  have hx:w R=0:=e; exact ⟨he,hx,by rw [hx, zero_sub,norm_neg]; exact (z.connected Y H D G room χ s M).1⟩
/-- Use a publisher on global Cloud when desired. This is the very cost on the LOCAL physical word. -/
theorem Cloud_price (t:Altitude.Cloud (Dome (tent Y H)) →ₗ[ℂ] ℂ)(w:rule Y H M W
    (t.comp ((pinhole Ξ s).toLinearMap.comp (Bay K P).val.toLinearMap)) (α)) :
    t ((φ f)*(φ g))=0 ∧ Φ < ‖t ((φ f)*(φ g))-Γ ((φ f)*(φ g))‖:= by
   obtain ⟨e,v⟩:= failure_pair Y H D G room χ s M W z _ w
   rw [norm_sub_rev] -- symmetrical, expose cost of t itself
   rw [←map_mul (pinhole Ξ s)]; exact ⟨e,v⟩
end Comparison
end Siam
end YM.CF.Buffered.Afterglow.Tower.Selection.Home
open YM.CF.Buffered.Afterglow.Tower.Selection.Home.Siam.Comparison
#print axioms pure_charge_bill
#print axioms failure_pair
#print axioms ofSinglet
#print axioms Cloud_price
#print axioms prices_fit
#print axioms projector_exists
