import Anomaly.Framing.Folk
import YM.SU5.Silk.Clock.Medal
import YM.SU5.Exchange.Pilot.Contour
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Sour.Turning
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Urn Hake Pastry Salt Hive Vow Skye Scion Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra loreM loreN
variable {n:Side}{p:RG.BudgetPoint}(s:Sweep n)
open Ione Ione.Clock
local notation "Vn" => Finset (Dwell n)
local notation "Fξ" => Firing n
local notation "Vs" => Support (More n)

def fireTurn(s:Sweep n)(V: Firing n): Firing n:=fun x=> sauce s.charge (detX s.s) (γS s) (V (yellA s⁻¹ x))
lemma step_turn (W: Fξ) (x:Orbit n): fireTurn s W (yellA s x)=sauce s.charge (detX s.s) (γS s) (W x) :=by unfold fireTurn; rw [show yellA s⁻¹ (yellA s x)=x from Prod.ext (revB ..) (tuftT ..)]

lemma pillarCost (u:s∈Whirl n) :∃ l:Equiv.Perm (Finset (Dwell n)),
    (∀ i:Vn,(l i).card=i.card) ∧ (∀ i,‖(hail_Q s).val (l i) i‖≤1) ∧
    ∀ (M:FC (Dwell n))(i j:Vn),sauce s.charge (detX s.s) (γS s) M (l i) (l j) = ((hail_Q s).val (l i) i* star ((hail_Q s).val (l j) j)) * (cSignX (s.charge.xor (detX s.s)) (M i j)) := by
  let A:= hail_Q s
  obtain ⟨l,t⟩:= Ione.Clock.nice_eq A (column_spin s u)
  have he (i:Vn): A.val (l i) i ≠0 :=by
    intro g; have ht:= Matrix.ext_iff.mpr (show star A.val*A.val=1 from A.property.1) i i
    have hx(j): A.val j i=0:=by by_contra p; exact p ((t j i p) ▸ g)
    simp [Matrix.mul_apply,hx] at ht
  refine ⟨l,fun i=> Ione.inkE _ _ _ (he i),fun i=>(norm_entry ..).trans (CStarRing.norm_of_mem_unitary A.property).le,?_⟩
  have ht (i j:Vn)(p:j≠i): A.val (l i) j=0:=by by_contra h; exact p (l.injective (t _ _ h).symm)
  intro M i j; unfold sauce; rw [singT,twist_formula]; let K:=windX (s.charge.xor (detX s.s)) M
  change ((A.val * K)* star A.val) _ _ = _; rw [Matrix.mul_apply,Finset.sum_eq_single j]; swap
  · intro k _ v; change _ * star (A.val (l j) k)=0; rw [ht j k v,star_zero,mul_zero]
  swap; · simp
  rw [Matrix.mul_apply,Finset.sum_eq_single i]; swap; · intro k _ v; rw [ht i k v,zero_mul]
  swap; · simp
  rw [mul_right_comm]; unfold K; cases s.charge.xor (detX s.s) <;> rfl -- let-bound K isn't dependent? check

abbrev tollPull (s:Sweep n)(i:Orbit n)(g:Seat n→E):= ((polarT s.charge ∘g) ∘ (castX s).anon n)
lemma kind_G (V:Orbit n)(g:Seat n→ E): yellA s (Lattice.gauge g V.1, threadG g V.2)=(Lattice.gauge (tollPull s V g) (flashA s V.1),threadG (tollPull s V g) (bun s V.2)):=by
    refine Prod.ext (revG ..) (funext fun i=> ?_); change bun s (threadG g V.2) i= threadG _ (bun s V.2) i; simp only [bun,man,threadG, map_mul,map_inv]; rfl
lemma kind_R(V:Orbit n)(g:Seat n→E): tollPull s⁻¹ V (tollPull s V g)=g := by
  funext i; change polarT s⁻¹.charge (polarT s.charge (g (boxA s (boxA s⁻¹ i))))= _
  rw [sitU,Equiv.apply_symm_apply,polar_t]; change polarT (s.charge ^^ s.charge) _= _; cases s.charge<;> rfl

variable {X Y:Aura n}{D:Support (More n)}{V:Firing n}{h a:ℝ}
open Rill Rue Jet
lemma carry_fares (sW:s∈ Whirl n)(q: Marque p (moldA s X) (moldA s Y) (actY s D) V h a)(hv:0≤h):
    Marque p X Y D (fireTurn s⁻¹ V) h (strive_E p.order*a):=by
  let C:= sauce s⁻¹.charge (detX s⁻¹.s) (γS s⁻¹)
  let G:=C ∘ V ∘ yellA s
  have hx:fireTurn s⁻¹ V=G:=by unfold fireTurn; simp only [inv_inv]; rfl
  rw [hx]
  refine ⟨⟨?_,fun v=>?_,?_,?_⟩,?_⟩
  · refine Measurable.comp ?_ (q.cog.comp (((revM s).measurable.comp measurable_fst).prodMk ((tuft s).measurable.comp measurable_snd)))
    let A : FC (Dwell n) →ₗ[ℝ] FC (Dwell n):=⟨(lotY s⁻¹.charge (detX s⁻¹.s) (γS s⁻¹)).toAddMonoidHom,fun r w=> by -- Real linear
       change C (r • w)=r • C w; simp only [C,sauce,singT,win_r,map_smul]⟩
    exact A.continuous_of_finiteDimensional.measurable
  · have he:= spin_step_e ((moldA s Y).val) _ s⁻¹ (q.body (yellA s v))
    rw [show actY s⁻¹ (moldA s Y).val=_ from tape_C s Y.val] at he; exact he
  · intro i j v w l g'; let T i:= yellA s i; obtain ⟨l',g⟩:= yellow s i j X.val l g'; exact congrArg C (q.same (T i) (T j) ((lights_C ..).mpr v) ((lights_C ..).mpr w) l' g)
  · intro i t u; let x:= yellA s i; let F:= tollPull s i t
    unfold G Function.comp; rw [kind_G]; have ht:V (Lattice.gauge F x.1,threadG F x.2)=sauce false false (tradew n F) (V x):=q.gauge x F ((lights_C ..).mpr u)
    change C (V (Lattice.gauge F x.1,threadG F x.2))= _; rw [ht]
    have hz: lotY false false (tradew n (tollPull s⁻¹ i F)) (C (V x))=C (sauce false false (tradew n F) (V x)):= spin_gauge s⁻¹ F (q.body x)
    unfold F at hz; rw [kind_R] at hz; exact hz.symm
  obtain ⟨T,u,g,v⟩:=q.vet
  let a':= strive_E p.order
  have hz:0≤a':= by unfold a' strive_E composeCost; positivity
  obtain ⟨l,L,S,y⟩:=pillarCost s⁻¹ (inv_mem sW)
  let U(i j:Vn):=a' * T (l.symm i) (l.symm j)
  refine ⟨U,fun i j=>mul_nonneg hz (u ..),?_,?_⟩
  · intro j; obtain ⟨j,rfl⟩:= l.surjective j
    unfold Rail; rw [show (∑ i:Vn, _)= a' * (∑ i:Vn,h^i.card*T i j) from ?_, L,mul_assoc (strive_E p.order) a]; exact mul_le_mul_of_nonneg_left (g _) hz
    rw [Finset.mul_sum]; symm; refine Finset.sum_equiv l (by simp) (fun i _=>?_); change a'*(h^i.card*T i j)=h^(l i).card*_ ; unfold U; rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply,L]; ring
  intro W r A hK i j
  obtain ⟨i,rfl⟩:=l.surjective i; obtain ⟨j,rfl⟩:=l.surjective j
  let e(v:tangD n):= V (pressQ p (actY s A) (flashA s W.1) v, bun s W.2)
  let K:=door_b s W.1
  let N:= hail_Q s⁻¹
  let c:=N.val (l i) i * star (N.val (l j) j)
  let b:=(s⁻¹.charge.xor (detX s⁻¹.s))
  have e' (z:tangD n): G (pressQ p A W.1 z,W.2) (l i) (l j)=c • ((cast_B b) (e (K z) i j)):=by
    unfold G; simp only [Function.comp_apply, yellA,parl_v]; rw [castT]; exact y _ _ _
  simp_rw [e']
  let Q:= v (yellA s W) ((lights_C ..).mpr r) (actY s A) (map_subset_map.mpr hK) i j
  have hC:‖c‖ ≤1:=by unfold c; rw [norm_mul,norm_star]; exact mul_le_of_le_one_right (norm_nonneg _) (S j) |>.trans (S i)
  have hk:‖K‖≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=> by rw [one_mul]; exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun b=> (cod_E s W.1 i b).trans_le (norm_le_pi_norm ..)
  let η:= composeCost p.order (p.order.factorial*T i j) 1
  have hg:Pence p.order (fun v=>cast_B b (e (K v) i j)) 0 (a'*T i j):=by
    let Y'(v:tangD n):=e v i j; have he:Allows p.order Y' (K 0) ((p.order.factorial:ℝ)* T i j):= (map_zero K).symm ▸ Q.pay
    have HE:= he.comp (allows_linear hk (show ‖K 0‖ ≤ 1 from by rw [map_zero,norm_zero]; exact zero_le_one)); rw [show a'*_= _ from (show a'*T i j=((p.order:ℝ)+1)*η from by unfold a' η strive_E composeCost; ring)]
    apply Rue.bare_p _ η -- tune
    rw [←one_mul η]; exact HE.linear (cast_B b) (cap_X _)
  have ht:= hg.σ c
  unfold U; rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  exact ⟨ht.smooth, ht.earned.trans (mul_le_of_le_one_left (mul_nonneg hz (u ..)) hC)⟩
end YM.CF.Sour.Turning
