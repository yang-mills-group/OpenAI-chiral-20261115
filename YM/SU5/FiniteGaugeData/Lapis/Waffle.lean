import YM.SU5.FiniteGaugeData.Lapis.Hedge
import YM.Work.F03.Flat
import YM.Work.G06.TurnSlot
/-! # Frame. Ambient tangent Gaussian and projection prices for growth occupancy.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Lapis
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Punch
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical
namespace Lumi
open Next.Rank Next.Rank.Spindle CF.Font
variable {ι:Type}[Fintype ι][DecidableEq ι]{G:Gauge}(T:Duct G ι)(s:Signed)(i:ι){n:Side}(x:Site n){M:ℕ}{S:Finset Cover} {u t:ℝ} {K C:ℕ}{Z Y:Finset (Site n)}
-- aperture box (constant, paid before all high res)
def weave (q:Slot):ℕ:= q.length+ q.stencil.sup (fun x:Cover=> Finset.univ.sup (fun i:Axis=> (x i).natAbs))
def macroK(ι:Type)[Fintype ι](T:Duct G ι) := Finset.univ.sup (fun i:ι=> Finset.univ.sup (fun s: Signed=> weave (Γ T s i).1))
omit [DecidableEq ι]
local notation "m₀" => macroK ι T
local notation "H" => (Γ T s i).1
lemma length_q : (Γ T s i).1.length ≤ macroK ι T:= calc
    _ ≤ weave H:= Nat.le_add_right ..
    _ ≤ _:= by unfold macroK; apply le_trans (le_sup (f:=fun s:Signed=>weave (Γ T s i).1) (mem_univ s)) (le_sup _ (f:=fun i:ι=>Finset.univ.sup (fun s:Signed=> weave (Γ T s i).1))); exact mem_univ i
lemma resident(y:Cover)(v:y ∈ (Γ T s i).1.stencil): y∈ box (macroK ι T):=by
 let F:=(H); have he:=le_sup (f:=fun i:ι=> Finset.univ.sup (fun s:Signed=>weave (Γ T s i).1)) (mem_univ i); have hh: weave F≤ m₀:= (le_sup (f:=fun s:Signed=>weave (Γ T s i).1) (mem_univ s)).trans he
 let f(z:Cover):= Finset.univ.sup (fun i:Axis=> (z i).natAbs); have ht(j:Axis) : (y j).natAbs ≤ macroK ι T:= (le_sup (f:=fun i:Axis=> (y i).natAbs) (mem_univ j)).trans ((le_sup (f:=f) v).trans ((Nat.le_add_left ..).trans hh)); exact box_test.mpr ⟨fun i=> by specialize ht i; omega, fun i=> by specialize ht i; omega⟩
lemma nearby : (slotFace H x).1 ∈ Spindle.patch (macroK ι T) x := doors _ |>.2 ((Work.E04.slot_separation _ _).trans (length_q T s i)) -- args order.Work.E04.slotFace? 
lemma atRoom(j:Finset (Site n)){X Y:Config G n}(p:Agrees (Spindle.patch (macroK ι T) x) X Y) : (H).atSite X x= (H).atSite Y x := by
 apply Slot.covered; intro z a b; let q:Bond n:= (wrap n z.1+x,z.2); apply p q (village_le _ (resident T s i z.1 a)); apply (Eq.subst _ (village_le (b:=macroK ι T) (o:=x) (z.1+step z.2) (resident T s i (z.1+step z.2) b))) -- tune
 unfold q; dsimp only; rw [map_add,wrap_step]; abel
-- one epoch chart concentration. polynomial s; no Foot threshold cut, hol through all epochs
lemma wake (G:Gauge)(w:ℕ) : ∃ C d:ℝ,0 ≤ C ∧ 0 < d ∧ ∀ n:Side,∀ (X:LogField G n)(x:Site n)(s:Slot),s.length≤ w→‖X‖≤d→‖s.atSite (represent X) x-faceCurl (slotFace s x) X‖ ≤ C* ‖X‖^2:=by
 obtain ⟨A,d,hA,hd,ha⟩:= face_chart_cost G; obtain ⟨B,r,hB,hr,hb⟩:=chord_chart_cost G; let D:= 2*G.colorScale* B*(w:ℝ); let C:= A*(1+D); have hD:0≤D:= by have h:= G.colorScale_pos; unfold D; positivity
 refine ⟨C,min d r, (by unfold C; positivity), lt_min hd hr,?_⟩; intro n a q s h e; let x:=slotFace s q; let y:=faceCurl x a; let u:=G.curvature (faceValue (represent a) x); let U:=travel (represent a) q s.walk; let g:=‖a‖
 have hh(i:Edge (Site n)): G.chord (represent a i) ≤ B*g:=by
    have ht:= norm_le_pi_norm a (markZ n i); rw [represent_link]; exact (hb _ (ht.trans (e.trans (min_le_right ..)))).trans (by change B* ‖a (markZ n i)‖≤ B*g; exact mul_le_mul_of_nonneg_left ht hB.le)
 have ht : G.chord U ≤ w*(B*g):= (travel_chord (represent a) s.walk q (B*g) hh).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (le_trans (show s.walk.length ≤ s.length from by unfold Slot.length; omega) h)) (by unfold g; positivity))
 have hm:2*G.colorScale*G.chord U≤ D*g:= by apply (mul_le_mul_of_nonneg_left ht (show 0 ≤ 2*G.colorScale by have :=G.colorScale_pos; positivity)).trans_eq; unfold D; ring
 obtain ⟨v,z⟩:= ha a x; rw [atSite_path]; change ‖G.adjoint U u-y‖≤ C*g^2; calc
    _≤‖G.adjoint U u - G.adjoint U y‖ + ‖G.adjoint U y-y‖:=norm_sub_le_norm_sub_add_norm_sub ..
    _≤ A*g^2+ D*g*(A*g):= add_le_add (by rw [←map_sub,G.norm_adjoint]; exact z (e.trans (min_le_left ..))) ((adjoint_norm_sub U y).trans (mul_le_mul hm v (norm_nonneg _) (mul_nonneg hD (norm_nonneg a))))
    _ = _:=by unfold C; ring
end Lumi
end YM.SU5.FiniteGaugeData.Lapis
#print axioms YM.SU5.FiniteGaugeData.Lapis.Lumi.wake
