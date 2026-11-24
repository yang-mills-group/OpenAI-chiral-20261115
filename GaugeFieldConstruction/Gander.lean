import GaugeFieldConstruction.Clockup
import GaugeFieldConstruction.Hindu
/-!
# money on polynomial representatives. Cost powers through 3 labels.
-/
set_option autoImplicit false
set_option maxHeartbeats 45000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.FlightFlux
open Function Filter Metric Lattice Wilson RG OrderedFinpartition Gauge Laurent Bloch Precision Tree Next.Free HarmP Pressure
open Planned.PrimaryIntegral295 Carrier
open AnalyticBridge.VerifiedReset
open scoped ContDiff Topology InnerProductSpace BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {c n f:Side}{G:Gauge}{S:StepData c f}{T: Tube G S}{a k v z:ℝ}
open CF.Skye CF.Scree CF.TableF CF.TableF.Axon
variable (P:BudgetPoint)
open PhysicalNext.JointLoad MultiNext.SignedSource Lyre
lemma basisF_3 (p:P.power=3)(f: Wheel Axis G.Color)(o:Site n)(h:0≤ a)(l:∀ i x,‖f i x‖≤ a*P.threshold * (1+lateral x)^3): Sized (64*a) (camW o f) P o:=by
 have he:0≤P.threshold:= P.threshold_pos.le; refine ⟨by positivity,fun i=>?_⟩; unfold camW
 unfold Lyre.width; rw [p]; apply (l ..).trans; let u:=stem o i.1; let N:ℝ:=separation i.1 o; have hN:0 ≤ N:=Nat.cast_nonneg _; have hx:(lateral u:ℝ)≤4*N:=by unfold N u; exact_mod_cast stem_t o i.1
 have hu:(1:ℝ)+lateral u≤ 4*(1+N):=by linarith
 apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hu 3) (mul_nonneg h he)).trans_eq; ring
abbrev StrongE (P:BudgetPoint)(X:Hub n)(a z:ℝ)(U:tangD n):Prop:=∃ f: Fin 4→ tangD n, U=∑ i,f i∧ ∀ i:Fin 4, Sized (a*z^(i.val+1)) (f i) P X.val.1∧(i.val<3→ PollenG P X (a*z^(i.val+1)) (f i) (i.val+1))
variable {P}
lemma StrongE.tap {X:Hub n}{U:tangD n}(p:StrongE P X a z U):Footmark P X a z U:=by obtain ⟨X,h,t⟩:=p; exact ⟨X,h,fun i=>⟨(t i).1,fun k=>((t i).2 k).foot⟩⟩
set_option maxHeartbeats 120000 in
lemma Carve (U:tangD n)(a₀:Hub n)(p:P.power=3)(C:ℝ)(c:0≤C)(hz:0 < z)(e:z≤1)(b:∀ i:Axis,Goose Dignity.norm (C*z*P.threshold) z (fun j=> W_form _ _ U a₀.val.1 j i) 3): StrongE P a₀ (64*12*C) z U:=by -- tune p binder
 let T:= P.threshold; let K:=C*z*T; let o:= a₀.val.1; let Q(i:Axis)(x:Cover):= W_form _ _ U o x i; let w₀(i):= curb (Q i); let w₁(i):=slopeK (Q i); let w₂(i):=ticketK (Q i); let w₃(i):=Q i-wheelK (Q i) 3;
 have ht(i l)(h:l.length≤3):‖loom l (Q i) 0‖≤ K*z^l.length:=by have he:=(b i).H (x:=0) l h; simpa only [lateral_zero,Nat.cast_zero, mul_zero,add_zero, one_pow,mul_one] using he -- tune bind
 have hs:= P.threshold_pos; have hv:0 ≤ K:=mul_nonneg (by positivity) hs.le
 have hh(i): ‖Q i 0‖ ≤ K := by have he:= ht i [] (by simp); simpa [loom,List.foldr] using he
 have hg(i j): ‖advance j (Q i) 0‖ ≤ K*z:=by simpa only [loom_cons,show loom [] (Q i)= Q i from rfl, List.length_cons,List.length_nil,Nat.zero_add,pow_one] using ht i [j] (by simp)
 let k:= 64*12*C; have hk: C ≤ k:=by unfold k; linarith
 have hx(n:ℕ): 64*(12*(C*z^n))=k*z^n:=by unfold k; ring
 let W:= (![w₀,w₁,w₂,w₃]:Fin 4→ Wheel Axis CF.SU.group.Color); let F(j):=camW o (W j); -- need p unresolved angle syntax
 refine ⟨F,?_,fun i=>?_⟩
 · funext x; rw [Finset.sum_apply, Fin.sum_univ_four]; let H:=stem o x.1; change U x=w₀ x.2 H+w₁ x.2 H+w₂ x.2 H+w₃ x.2 H; change U x=_+_+_+(W_form _ _ U o H x.2-(w₀ x.2 H+w₁ x.2 H+w₂ x.2 H)); rw [show W_form _ _ U o H x.2= U x from (by unfold W_form; rw [show wrap _ H=_ from wrap_lift (x.1-o)]; rw [add_sub_cancel])]; abel -- tune lemma add_sub_cancel
 constructor
 · rw [show _= 64*(12*(C*z^(i.val+1))) from (hx _).symm]; apply basisF_3 P p (W i) o (by positivity); intro j x; let y:ℝ:=lateral x; have hy:0 ≤ y:=Nat.cast_nonneg _; have he : 1 ≤ (1+y)^3:=one_le_pow₀ (by linarith); have hs : y ≤ (1+y)^3:=(le_add_of_nonneg_left zero_le_one).trans (le_self_pow₀ (by linarith) (by decide));
   have hy':y^2 ≤ (1+y)^3:=by refine (pow_le_pow_left₀ hy (le_add_of_nonneg_left zero_le_one) 2).trans (pow_le_pow_right₀ (by linarith) (by decide))
   fin_cases i
   · change ‖Q j 0‖≤ 12*(C*z^1)*T*(1+y)^3; rw [pow_one]; apply (hh j).trans; apply le_trans (b:=K*(1+y)^3) (le_mul_of_one_le_right hv he); unfold K; nlinarith -- tune
   · change ‖slopeK (Q j) x‖ ≤12*(C*z^2)*T*(1+y)^3; apply (scaleStance Dignity.norm _ _ _ (hg j)).trans
     have hl:0≤K*z:=mul_nonneg hv hz.le; refine (mul_le_mul_of_nonneg_right hs hl).trans ?_; rw [show 12*(C*z^2)*T=12*(K*z) from (by unfold K; ring)]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (1+y)^3) hl]
   · change ‖ticketK (Q j) x‖ ≤12*(C*z^3)*T*(1+y)^3; let A:=K*z^2; have hh:0 ≤ A:=by unfold A; positivity; -- caution semi
     apply (GoldT Dignity.norm _ _ A hh (fun i k=>by simpa only [loom_cons,show loom [] (Q j)=Q j from rfl] using (show ‖loom [i,k] (Q j) 0‖≤ A from by change _≤ K*z^([i,k]:List Axis).length; exact (ht j [i,k] (by simp) )) )).trans; apply (mul_le_mul_of_nonneg_right hy' hh).trans; rw [show 12*(C*z^3)*T=12*A from (by unfold A K; ring)]; nlinarith [mul_nonneg hh (by linarith : 0 ≤ (1+y)^3)]
   change ‖((Q j)-wheelK (Q j) 3) x‖ ≤12*(C*z^4)*T*(1+y)^3; apply (Goa_total Dignity.norm (Q j) K z _ le_rfl x (b j) e).trans_eq; unfold K T y; ring
 intro h; refine ⟨W i,⟨fun j _ _=>rfl,fun j=>?_⟩,?_,?_⟩
 · fin_cases i
   · change ‖Q j 0‖ ≤ k*z^1*T; rw [pow_one]; exact (hh j).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hz.le) ‹0<P.threshold›.le)
   · unfold W; simp [slopeK,w₁,slope₀]; positivity -- tune
   · unfold W; simp [ticketK,w₂,ticket₀]; positivity -- tune
   change 3<3 at h; omega
 · intro k'; fin_cases i
   · exact curb_paper (Q k')
   · change Paper 2 (slopeK (Q _)); unfold slopeK; apply slope_paper
   · change Paper 3 (ticketK (Q _)); unfold ticketK; apply ticket_paper
   change 3<3 at h; omega
 intro j L
 fin_cases i
 · change ‖advance j (curb (Q L)) 0‖≤ _; rw [show advance j (curb (Q L))= 0 from advance_const ..,Pi.zero_apply,norm_zero]; positivity -- tune
 · change ‖advance j (slopeK (Q L)) 0‖ ≤ k*z^2*T; rw [slopeK,φ_step]; apply (hg _ _).trans; rw [show K*z=C*(z^2*T) from (by unfold K; ring)]; exact ((mul_le_mul_of_nonneg_right hk (show 0 ≤ z^2*T from mul_nonneg (by positivity) ‹0<P.threshold›.le)).trans_eq (mul_assoc k _ _).symm) -- tune K rearrange
 · change ‖advance j (ticketK (Q L)) 0‖≤ k*z^3*P.threshold; rw [tear_t,slopeK,slope₀,norm_zero]; positivity
 change 3<3 at h; omega
variable (P)
local notation "GS"=> CF.SU.group
-- cast driver API for exact occurrence. vary length proof transport
omit P
def Signature_p (S:StepData c f)(T:Tube G S)(k:ℝ)(P:Flight 4 4):Prop:= ∃ v:P.L=S.patch.L,v ▸ (linesOf P k)=T.R.A0 -- tune HEq
lemma FirmU_l (A B:Side)(v:A=B)(f:Lines A)(h:Whole f)(V:Lines B)(g:HEq f V): Whole V:=by subst B; rw [← eq_of_heq g]; exact h -- tune
lemma g_up (L F:Side)(h:F=L)(p : Lines F)(q:Lines L)(u: HEq p q)(f:Window G.Color) (x:Site F)(y:Site L)(v:HEq x y): applyLine p f ∘ (fun z:Cover=> z+lift x)=applyLine q f ∘ (fun z=> z+lift y):=by subst L; rw [eq_of_heq u,eq_of_heq v] -- tune
lemma StrongCurve (k:ℝ)(p:0<k):∃ C:ℝ,1≤C∧∀ (c f:Side)(S:StepData c (CF.Cube.More f))(P:BudgetPoint)(T:Tube GS S)(R:Flight 4 4),R.L=S.ratio.count → HEq (linesOf R k) T.R.A0 → ∀ (Z:CF.Scree.Hub f)(F:Directions GS c)(t:ℝ),0≤ t → P.power=3 → Heir.Limb 3 (S.ratio.parent Z.val.1) F (t*P.threshold)→ StrongE P Z (C*t * SpanL R.L) ((R.L.val:ℝ)⁻¹) (Heir.route T F) :=by
 obtain ⟨C,hc,H⟩:=Capac (E:= CF.SU.group.Color) k p; refine ⟨64*12*C,(by linarith),fun c f S P T R u v Z F t h k' l=>?_⟩
 let X:= F; let o:= Z.val.1; let L:= S.ratio.count; let r:= S.ratio.residue o; let W: Window CF.SU.group.Color:=W_form _ _ F (S.ratio.parent o); let A:Lines L:=T.R.A0
 obtain ⟨y,hy⟩ : ∃ y: Site R.L, HEq y r:=by exact (show ∀ i:Side,i=L→∃ y: Site i, HEq y r from fun i h=>by subst i; exact ⟨r,HEq.rfl⟩) R.L u -- tune
 have hp:=P.threshold_pos; let D:=C*t*SpanL R.L; have hz:0 ≤ D:=by unfold D; have he:=span_one R.L; positivity
 rw [show 64*12*C*t*SpanL R.L=64*12*D from (by unfold D; ring)]
 let hT := FirmU_l R.L L u (linesOf R k) (stored R k p le_rfl) A v
 apply Carve _ _ k' D hz (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast R.L.property)); intro i
 rw [show W_form _ _ (Heir.route T F) Z.val.1= applyLine (linesOf R k) W ∘ (fun z:Cover=> z+lift y) from ((Route_home S T hT F o).trans (g_up L R.L u (linesOf R k) A v W y r hy).symm)] -- tune
 let z:ℝ:=(R.L.val:ℝ)⁻¹; change Goose Dignity.norm (D*z*P.threshold) z _ _; rw [show D*z*P.threshold=C*(t*P.threshold)*z*SpanL R.L from (by unfold D; ring)]; exact H R _ W (Lifter _ F (mul_nonneg h hp.le) l) y i
end YM.FlightFlux
end
