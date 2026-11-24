import Anomaly.Basis.Grid
import YM.CF.Swell.Fist
/-! PH columns. keep their ownership even on wrong polar slots for null purchases. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell.Porticus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
variable {N B M:Side}{Y:SOp N}{S:Sa N}{P:BudgetPoint}{a t d f h p' x₀ y s:ℝ}{k p q:ℕ}{K:Scree.Loom N}
local notation "I"=> Single N
local notation "θ"=> More N
open Buffered TreasuryFog Vow.TreasuryFog
variable {V:SOp N}{o: Site N}{A:Op (Single N)}{φ μ g₀:ℝ}
-- broaden Branded law.or if want PH away root with short halo no? just these.
abbrev Tucked (o:Site N)(A:Op (Single N)):Prop:=∀ i j:Single N,A i j≠0→ node o=node i.1.1 ∨ node o=node j.1.1
variable (p₀:Fit o p k f A)(hA:Tucked o A)
include p₀ hA
lemma eyeΖ(i j:Prism.Rock N)(u: boxM A i j≠ 0): (Λrod i j).length ≤16*k ∧node o∈χrod i j:=by
 obtain ⟨p,q,h⟩:∃ p q:SU.Slot,A (i,p) (j,q)≠0:=by by_contra! v; exact u (Matrix.ext fun i' j'=> v i' j')
 have hx:= separation_triangle (node i.1) (node o) (node j.1); have hp:= p₀.2.2 _ _ h; have ht:= hA _ _ h
 have he: separation (node i.1) (node j.1) ≤4*k:=by rw [separation_comm (node i.1) (node o),Hove.ζdist o i.1,Hove.ζdist o j.1] at hx; change separation o i.1≤k ∧ separation o j.1≤k at hp; omega
 refine ⟨(Font.short ..).trans (by omega),?_⟩
 cases ht with|inl h=>rw [h]; exact trace_source ..|inr h=> rw [h]; exact (show stop (node i.1) (Λrod i j)=node j.1 from stopH ..) ▸ trace_last (node i.1) (Λrod i j)
-- narrow. supports only. even chirality elsewhere
lemma Ωcoat (v: 0<d) (u:d≤1) (s:0 ≤ a): Soak (node o) (ρlens A) a (νt a d (16*k)*(Haro.horn*f)) d:=by
 let X:= A; let l:=k; let M(p q:Rock N):= κfare p q d (boxM X p q); let V(p q:Rock N):= Tulip.reed p q (M p q); let W:=νt a d (16*l); have ht: 0 ≤ W:=by unfold W νt; positivity
 have hf(p q:Rock N)(l':boxM X p q=0): V p q=0:=by unfold V M; rw [l']; funext i j; simp [Tulip.reed, κfare]
 refine arm_v (o:=node o) (fun j:Rock N×Rock N=> χrod j.1 j.2) _ (fun j=>V j.1 j.2) (fun j=>Ωg j.1 j.2 d v u X p₀.2.1) ?_ ?_ (fun i=>?_ ) -- adapted Fist
 · have hh:=cute o p X
   apply le_trans _ (mul_le_mul_of_nonneg_left (hh.trans (mul_le_mul_of_nonneg_left p₀.1 (zero_le_one.trans Haro.p0))) ht); rw [Fintype.sum_prod_type,mul_sum]; apply sum_le_sum; intro i _; rw [mul_sum]; apply sum_le_sum; intro q _; by_cases hx:boxM X i q=0; · change rent a (χrod i q)* ledgerV (V i q)≤ W*_; rw [hf _ _ hx,hx,norm_zero]; simp [ledgerV]
   have he:= (eyeΖ p₀ hA i q hx).1; let n:ℕ:=(Λrod i q).length; let t:ℝ:= Real.exp (a*((16*l+1:ℕ):ℝ)); have hz:rent a (χrod i q)≤ t:=Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ((trace_k ..).trans (Nat.add_le_add_right he _))) s)
   rw [show ledgerV (V i q)=(Fintype.card SU.Slot:ℝ)^2*M i q from box_phi i q i]; apply le_trans (mul_le_mul_of_nonneg_right hz (mul_nonneg (sq_nonneg _) (show 0 ≤ M i q from (by unfold M κfare; positivity))))
   change t* ((Fintype.card SU.Slot:ℝ)^2*((n+1:ℝ)*(1+d)^n* ‖boxM X i q‖)) ≤ W* _; unfold W νt; calc
    _ ≤ t*((Fintype.card SU.Slot:ℝ)^2*((↑(16*l:ℕ)+1:ℝ)*(1+d)^(16*l) * ‖boxM X i q‖)) :=by gcongr; linarith
    _ = _:=by unfold t; ring
 · intro p v; apply hf; by_contra t; exact v ((eyeΖ p₀ hA p.1 p.2 t).2)
 rw [Fintype.sum_prod_type]
-- full line aggregated on core. post, preserve exact power h^2. No need nonwrapping to genotype. It isn't curling through TRUNK.
variable {j:ℕ}
local notation "QΨ"=> faceD true false (n:=_)
-- coefficient germs trust.S
private lemma warmε(i j:Rock N)(V:Chin N)(u:boxM A i j=0) : Φp i j A V=0:=by unfold Φp Swell.arm; rw [u,zero_mul]; ext i j; unfold Tulip.panel; simp
lemma knit_C (Z:Aura N)(B: halo (16*k+1+q+10) {node o}⊆ Z.val)(T:DockPulse P K t d a h s j q)(v:d≤1): Herb P q Z h (shipInc K (ρlens A) (faceD true false)) (vaporB P h (νt a d (16*k)*(Haro.horn*f))):=by
 let l:=k; let Y:=A
 let V(i j:Rock N):= κfare i j d (boxM Y i j); let F(i j:Rock N):= Φp i j A; let E(i j:Rock N):= shipInc K (F i j) (faceD true false); let Nq:ℝ:=νt a d (16*k); let x:= T.pos; let X:=T.hint; let y(p q:Rock N):=V p q; let B'(p q:Rock N):=Tulip.reed p q (V p q)
 have hz(i j:Rock N)(w:boxM Y i j=0): B' i j=0:=by unfold B' V; rw [w]; funext i j; simp [Tulip.reed,κfare]
 have hU(p q:Rock N): ledgerV (B' p q)≤ Nq*‖boxM Y p q‖:=by
    rw [show ledgerV (B' p q)=(Fintype.card SU.Slot:ℝ)^2*V p q from box_phi p q p]; by_cases u: boxM Y p q=0; · unfold V; rw [u,norm_zero]; unfold κfare; rw [norm_zero]; simp
    obtain ⟨y,w⟩:=eyeΖ p₀ hA p q u; let n:= (Λrod p q).length; let s':=(Fintype.card SU.Slot:ℝ); unfold V; change s'^2*((n+1:ℝ)*(1+d)^n*_ )≤ _
    calc
     _ ≤ s'^2*((↑(16*k:ℕ)+1:ℝ)*(1+d)^(16*k)*‖boxM Y p q‖) :=by gcongr; linarith
     _ ≤ Real.exp (a*((16*k+1:ℕ):ℝ))*(s'^2*((↑(16*k:ℕ)+1:ℝ)*(1+d)^(16*k)*‖boxM Y p q‖)):= le_mul_of_one_le_left (by positivity) (Real.one_le_exp (by positivity))
     _ = _:=by unfold Nq νt s'; ring
 let Φ(S:Op I):= faceD true false S; let Qc(i j:Rock N):= vaporB P h (ledgerV (B' i j)); let R:=Φ; obtain ⟨m,b,w,hb⟩:= T.room
 have hp(i u:Rock N): Herb P q Z h (E i u) (Qc i u):=by
    by_cases p:boxM Y i u=0
    · have he:E i u=0:=by funext V; unfold E F shipInc; rw [warmε p₀ hA i u _ p]; simp only [(pal_v _ T.high).whirl, Matrix.zero_apply,zero_smul,sum_const_zero]; rfl
      rw [he,show Qc i u=0 from by unfold Qc; rw [hz i u p]; simp [ledgerV,vaporB]]; exact Herb.zeroR
    apply Herb.kernelR T.roof T.pos _ _ (Ωg i u d x v A p₀.2.1) (pal_v _ T.high) T.reach w hb T.fees T.most
    intro v t; obtain ⟨z,g,a⟩:= halo_spec.mp t; obtain ⟨n,s⟩:=eyeΖ p₀ hA i u p
    have hx: separation (node o) z < (χrod i u).card:= (trace_g (node i.1) (Λrod i u)).lim (node o) s z g
    have ht:= (trace_k (node i.1) (Λrod i u)); change (χrod i u).card ≤ _ at ht
    exact B (halo_spec.mpr ⟨node o,mem_singleton_self _,(separation_triangle _ z _).trans (by omega)⟩)
 rw [show shipInc K (ρlens A) (faceD true false)=∑ i:Rock N,∑ j:Rock N,E i j from ?_]
 · apply (Herb.whole _ _ _ (fun i _=> Herb.whole _ _ _ (fun j _=> hp i j))).large_r (zero_le_one.trans T.high)
   unfold Qc vaporB; simp_rw [←sum_mul,←mul_sum]; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) (sq_nonneg _)
   apply (sum_le_sum (fun i _=>sum_le_sum (fun j _=> hU i j))).trans; simp_rw [←mul_sum]; refine mul_le_mul_of_nonneg_left ((cute o p Y).trans (mul_le_mul_of_nonneg_left p₀.1 (zero_le_one.trans Haro.p0))) (by unfold Nq νt; positivity)
 funext V; unfold shipInc ρlens; simp_rw [Finset.sum_apply]; unfold E shipInc F; simp_rw [(pal_v _ T.high).whirl,Matrix.sum_apply, sum_smul, sum_comm (s:=(univ:Finset I)) (t:=(univ:Finset (Rock N)))]; -- tune reorder
-- stamp I from Core analytic. flat U.e Energy exactly.
lemma profile_bind (Z:Aura N)(B: halo (16*k+1+q+10) {node o}⊆ Z.val)(T:DockPulse P K t d a h s j q)(e:d≤1)(x:Orbit N)(u:pingS P.threshold Z.val x.1):ρlens A (profile (K x))=ρlens A (profile x.1):=by
 unfold ρlens; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; by_cases h:boxM A i j=0; · rw [warmε p₀ hA i j _ h,warmε p₀ hA i j _ h]
 obtain ⟨t,w⟩:=eyeΖ p₀ hA i j h
 have hr:halo (q+10) (χrod i j) ⊆ Z.val:=by intro k y; obtain ⟨l,m,q'⟩:=halo_spec.mp y; have ht: (χrod i j).card ≤ (Λrod i j).length+1:=trace_k ..; exact B (halo_spec.mpr ⟨node o,mem_singleton_self _,(separation_triangle _ l _).trans ((add_le_add ((show separation (node o) l<(χrod i j).card from (trace_g ..).lim (node o) w l m)).le q').trans (by omega))⟩)
 unfold Φp Swell.arm; have hp: Agrees (χrod i j) (K x) x.1:=by let Q: x.1∈Sour.σX P Z ∅:=⟨by rw [sdiff_empty]; exact u,empty_subset _⟩; exact fun i t y=> fern T.roof T.reach _ hr _ Q i t rfl x.2
 rw [show Tulip.track (profile (K x)) (node i.1) _= Tulip.track (profile x.1) (node i.1) (Λrod i j) from ?_]; -- prove via Path.
 rw [track_pr,track_pr]; apply congrArg; exact Lattice.travel_local _ _ _ _ (fun e p q=> hp e (List.mem_toFinset.mpr p) (List.mem_toFinset.mpr q))
end YM.CF.Swell.Porticus
