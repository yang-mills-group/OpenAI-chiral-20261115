import YM.SU5.Exchange.Reg.Union
import YM.CF.Milo.Cent
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
open Vow Salt
variable (P:BudgetPoint)(s:Sweep n)
local notation "Ta"=> actY s
local notation "HQ"=> (hail_Q s).val
local notation "Φg"=> (Finset (Dwell n))
open Vow Larch
open Bake Lilt Rue Trees
variable (E:Pax n)(F:Pax n)(K:Cusp n)
local notation "T0"=> Sweep n
local notation "Γ"=> (plight_C n)
local notation "Hz"=> Scree.Hub n
-- root pension distribute. supports preserving regular total memory.
open Tenant
private lemma retreat (i : Hz) (F : InkD n) (t : PressB (raiseRate P) i F h a) :
 PressB P i F h a := by
 obtain ⟨b,f,q,r⟩:=t.worth
 exact ⟨t.term,t.fitted,t.measureV,t.gaugeV,b,f,fun V h i=>let q:=q V h i; ⟨q.grade,q.paid,q.token⟩,r⟩

abbrev massPlus (P:BudgetPoint)(δ:ℝ)(U:Support n)(x:ℝ) := Real.exp ((P.supportExponent+δ)*coverNumber P.B U) * x

lemma dial_middle (P : BudgetPoint)(F:RegBudget n) (u : IncX (fun _=>False) F P h a)
    (v : IncX (fun _=>False) F (raiseRate P) h 1)(p : 1 ≤ h)
    (hp : Real.exp (-(P.B:ℝ)/2) ≤ a)(hf : 40 ≤ P.B) :
    ∃ K:Hz→ℝ,(∀ i,PressB P i (F i) h (K i)) ∧
    ∀ x:Seat n, (∑ i:Hz, if x=i.val.1 then massPlus P (20/(P.B:ℝ)) i.val.2 (K i) else 0) ≤
       (Real.exp 20 + 1)*a := by
 obtain ⟨f,X,z⟩:=u.weight; obtain ⟨g,Y,w⟩:=v.weight
 let M(i:Hz):= if coverNumber P.B i.val.2 ≤ P.B then f i else g i
 have hb:0<(P.B:ℝ):= by exact_mod_cast P.B_pos
 have h2 : 0 ≤ h:=zero_le_one.trans p
 refine ⟨M, fun i=>?_, fun x=>?_⟩
 · unfold M; split; exact X i; exact retreat P i _ (Y i)
 rw [add_mul,one_mul]
 let t:= Real.exp (-(P.B:ℝ)/2)
 have he:=add_le_add (mul_le_mul_of_nonneg_left (z x) (Real.exp_pos 20).le)
   ((mul_le_mul_of_nonneg_left (w x) (Real.exp_pos _).le).trans (show t*1 ≤ a by simpa [t] using hp)) -- tune hp
 refine le_trans ?_ he; rw [mul_sum,mul_sum,←sum_add_distrib]; apply sum_le_sum; intro i _
 by_cases Q:x=i.val.1; swap; · simp only [if_neg Q,mul_zero,add_zero,le_rfl]
 simp only [if_pos Q]
 have hx:= (Taxi.eraF _ i (X i) h2 1 (ping_f P i.val.2)).grade
 have hg:= (Taxi.eraF _ i (Y i) h2 1 (ping_f (raiseRate P) i.val.2)).grade
 let k:ℝ:= coverNumber P.B i.val.2
 have hk:0 ≤ k := Nat.cast_nonneg _
 unfold M
 split
 next h=>
    apply le_add_of_le_of_nonneg _ (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le hg))
    unfold massPlus BudgetPoint.mass; rw [←mul_assoc, ←Real.exp_add]; gcongr
    change (P.supportExponent+20/(P.B:ℝ))*k≤20+ P.supportExponent*k
    have hb' : 20/(P.B:ℝ)*k ≤ 20:= le_trans (mul_le_mul_of_nonneg_left (show k≤P.B from Nat.cast_le.mpr h) (show 0 ≤ 20/(P.B:ℝ) by positivity)) (div_mul_cancel₀ _ hb.ne').le
    rw [add_mul,add_comm (P.supportExponent*k)]; linarith only [hb']
 next h=>
    apply le_add_of_nonneg_of_le (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le hx))
    unfold massPlus BudgetPoint.mass; rw [←mul_assoc, ←Real.exp_add]; gcongr
    have ht:40 ≤ (P.B:ℝ):= by exact_mod_cast hf
    have hz:20/(P.B:ℝ) ≤ 1/2:= (div_le_iff₀ hb).2 (by linarith)
    have hn:k≥ (P.B:ℝ):= Nat.cast_le.mpr (Nat.le_of_not_ge h)
    change _ ≤ (-(P.B:ℝ)/2)+ (P.supportExponent+1)*k
    dsimp [k] at *
    linarith only [hn, mul_le_mul_of_nonneg_right hz hk]

/-- polynomial expense for a square-radius anchor shift. -/
abbrev taxIns (B:ℕ):ℝ:=16*(16*Sour.fernL 4)*(B:ℝ)^10
lemma placeExpense {N:Side} (B:ℕ) (u:1≤B) (x: Site N):
 (∑ y:Site N, Real.exp (-((B:ℝ)^2)⁻¹/2*separation x y)) ≤ taxIns B:=by
 let q:ℝ:= ((B:ℝ)^2)⁻¹
 have e:1≤ (B:ℝ):=Nat.one_le_cast.mpr u
 have hq:0<q:=inv_pos.mpr (pow_pos (zero_lt_one.trans_le e) _)
 have ha:q≤1:=inv_le_one_of_one_le₀ (one_le_pow₀ e)
 let k:=univ.sup (separation x) + 1
 let H:= range k
 have hk(y:Site N):separation x y ∈ H:= mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (b:=y) (f:=separation x) (mem_univ _)))
 rw [←sum_fiberwise_of_maps_to (t:=H) (g:=separation x) (fun i _=>hk i)]
 calc
    _ ≤ ∑ i∈H,(16:ℝ)*(Real.exp (-q/2*i)*(i+1:ℝ)^4):=by
        apply sum_le_sum; intro i _; let δ:=Real.exp (-q/2 * i)
        let S:=univ.filter (fun y:Site N=> separation x y=i)
        have hf : S⊆ Branch.bay (terr N) x i:= fun j u=>(Branch.bay_mem i).mpr (mem_filter.mp u).2.le
        rw [sum_congr rfl (g:=fun _=>δ) (fun j (u:j∈ S)=>by rw [(mem_filter.mp u).2]),sum_const,nsmul_eq_mul]
        refine le_trans (mul_le_mul_of_nonneg_right ((Nat.cast_le.mpr (card_le_card hf)).trans (Tenant.reach x i)) (Real.exp_pos _).le) ?_
        unfold δ; exact le_of_eq (by ring)
    _ ≤ _:=by
        rw [←mul_sum]; apply le_trans (mul_le_mul_of_nonneg_left (Sour.pea q hq ha 4 k) (by norm_num)); exact le_of_eq (by unfold q taxIns; rw [inv_inv]; ring)

lemma inSeat (P:BudgetPoint)(x:Seat n)(i:Hz)(u:x∈i.val.2) :
  P.supportExponent* (coverNumber P.B i.val.2:ℝ)+10/(P.B:ℝ)*(coverNumber P.B i.val.2:ℝ)≤
 (-( (P.B:ℝ)^2 )⁻¹/2)* separation x i.val.1+1+(P.supportExponent+20/(P.B:ℝ))*(coverNumber P.B i.val.2:ℝ):=by
 let k:=coverNumber P.B i.val.2
 let d:=separation x i.val.1
 have hz:d≤k*(4*P.B+2)+2*P.B:= Corona.extent _ P.B u i.prop
 have hx:(d:ℝ) ≤ (k:ℝ)*(4*P.B+2)+2*P.B:=by exact_mod_cast hz
 let A:ℝ:= P.B; let n:ℝ:=k; let p:=P.supportExponent
 have he:1 ≤ A:= Nat.one_le_cast.mpr P.B_pos; have hp:0<A:=zero_lt_one.trans_le he
 have h : ((A^2)⁻¹/2)*(d:ℝ) ≤ 10/A*n+1:=by
    rw [inv_eq_one_div,div_div,mul_comm _ (d:ℝ),mul_one_div]; rw [div_le_iff₀ (by positivity : (0:ℝ)< _)] -- tune
    let Y : ℝ:=(10/A*n+1)*(A^2*2)
    change (d:ℝ) ≤ Y
    have hf:Y=20*n*A+2*A^2:=by unfold Y; field_simp; ring
    have hy:0≤ n:=Nat.cast_nonneg _; rw [hf]; refine le_trans hx ?_
    change n*(4*A+2)+2*A ≤ _; nlinarith
 change p*n+ 10/A*n ≤ -(A^2)⁻¹/2*(d:ℝ)+1+(p+20/A)*n
 rw [show 20/A=10/A+10/A by ring,add_mul,add_mul,neg_div,neg_mul]; linarith

abbrev annual (B:ℕ)(x:ℝ):ℝ:= taxIns B*(Real.exp 1*((Real.exp 20+1)*x))
lemma earnIncidence (P:BudgetPoint)(F:RegBudget n)
    (u : IncX (fun _=>False) F P h a)(v : IncX (fun _=>False) F (raiseRate P) h 1)(p : 1 ≤ h)
    (hp : Real.exp (-(P.B:ℝ)/2) ≤ a)(hf : 40 ≤ P.B) :
    ∃ K:Hz→ℝ,(∀ i,PressB P i (F i) h (K i)) ∧
    ∀ x:Seat n, (∑ i:Hz, if x∈i.val.2 then massPlus P (10/(P.B:ℝ)) i.val.2 (K i) else 0) ≤ annual P.B a:=by
 obtain ⟨K,hK,w⟩:=dial_middle P F u v p hp hf
 refine ⟨K,hK,fun x=>?_⟩; let X:=univ.filter (fun i:Hz=> x∈i.val.2); let Jw (i:Hz): Seat n:= i.val.1
 let μ(Z:Seat n):= Real.exp (-((P.B:ℝ)^2)⁻¹/2 * separation x Z); let C:= Real.exp 1
 have he:0≤ a:=(Real.exp_pos _).le.trans hp
 rw [←sum_filter, ←sum_fiberwise_of_maps_to (s:=X) (t:=univ) (g:=Jw) (fun _ _=> mem_univ _)]
 calc
    _ ≤ ∑ y:Seat n, μ y * (C*((Real.exp 20+1)*a)):=sum_le_sum fun y _=>by
       let V(i:Hz):= massPlus P (20/(P.B:ℝ)) i.val.2 (K i)
       let W(i:Hz):= massPlus P (10/(P.B:ℝ)) i.val.2 (K i)
       let Y:= X.filter (fun i=> Jw i=y)
       have hx(i:Hz):= (Taxi.eraF _ i (hK i) (zero_le_one.trans p) 1 (ping_f P i.val.2)).grade
       have hp(i:Hz)(p:i∈ Y):W i ≤ μ y * (C*V i):=by
          have hv:= inSeat P x i (mem_filter.mp (mem_filter.mp p).1).2
          rw [← (mem_filter.mp p).2]; unfold W V μ C Jw massPlus; rw [← mul_assoc (Real.exp 1),←mul_assoc,←Real.exp_add,←Real.exp_add]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (by linarith only [hv])) (hx i)
       apply (sum_le_sum hp).trans; rw [← mul_sum,←mul_sum]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
       apply le_trans _ (w y); rw [←sum_filter]
       exact sum_le_sum_of_subset_of_nonneg (fun i p=>mem_filter.mpr ⟨mem_univ _,(mem_filter.mp p).2.symm⟩) (fun i _ _=>mul_nonneg (Real.exp_pos _).le (hx i))
    _ ≤ _:=by
       rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (placeExpense P.B P.B_pos x) (by unfold C; positivity)
end YM.CF.Ione
