import YM.SU5.Gleam.Rounds
/-!
# Link orthogonality and conditional Gaussian integrands. On full-classified defects.
All real gauge fields for this bill. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X Y:fieldDir G n 1} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)
def room (T:Forest r) (F:Finset T.Free) (A:Support c)(m:ℕ) := innerBolts T F A (Sequest m+Sequest m)
abbrev Blip (T:Forest r) (F:Finset T.Free) := Regular T (fun x=> x∈ F)
abbrev deep (T:Forest r)(F:Finset T.Free) := freeze (G:=G) T (fun x=> x∈ F) -- don't use this implicit
variable {Y': LinkArray G (Blip T F)}
open scoped Classical
private lemma collection (e:Bond n)(t:↥F→G.Color): Exterior.collect G (stock T F t) e = ∑ i:↥F,(if e=i.val.val then t i else 0):=by
 let l:= turnBond n e
 change ∑ i:↥F,seatsF T F l i • t i= _; apply sum_congr rfl; intro i _; simp [seatsF,branchesZ,l]
lemma stock_clean (y:LogArray G F)(b:↥F):Exterior.collect G (stock T F y) b.val.val = y b:=by
 rw [collection]; have he(i:↥F): b.val.val=i.val.val ↔ b=i:=⟨fun p=>Subtype.ext (Subtype.ext p),fun p=>p ▸ rfl⟩; simp only [he]; rw [sum_ite_eq]; simp
lemma stock_shallow (y:LogArray G F)(e:Bond n)(h: ∀ b:↥F,e ≠ b.val.val): Exterior.collect G (stock T F y) e=0 :=by rw [collection]; simp only [if_neg (h _)]; simp
abbrev logX (U:Config G n)(e:Bond n):= G.plog (G.mat (U e))
def myLog (T:Forest r)(F:Finset T.Free)(Y: LinkArray G (Blip T F))(A:Support c): fieldDir G n 1:=
 fun x=> let e:= (turnBond n).symm x; if Working r A e ∧ ∀ i:↥F,e≠i.val.val then logX (T.drape (deep T F 1 Y)) e else 0
lemma myLog_field (A:Support c)(e:Bond n) : collect G (myLog T F Y' A) e=(if Working r A e ∧ ∀ i:↥F,e≠i.val.val then logX (T.drape (deep T F 1 Y')) e else 0):=by unfold collect myLog; rw [show (e.1,coord e.2)=turnBond n e from rfl, Equiv.symm_apply_apply]
lemma drapeX {X:LinkArray G F}(i:↥F) : T.drape (deep T F X Y') i.val.val=X i:=by rw [Forest.off_tree]; exact freeze_held T _ X Y' i --] -- use freeze
lemma drape_agrees {X:LinkArray G F}{e:Bond n} (p:∀ i:↥F,e≠i.val.val) : T.drape (deep T F X Y') e=T.drape (deep T F 1 Y') e:=by
 by_cases h:e∈T.trunks; · rw [show T.drape _ _= _ from T.on_tree (deep T F X Y') ⟨e,h⟩,show T.drape _ _= _ from T.on_tree _ ⟨e,h⟩]
 let v:T.Free:=⟨e,h⟩; let b:Blip T F:=⟨v,fun H=>p ⟨v,H⟩ rfl⟩; rw [show T.drape _ e= _ from T.off_tree (deep T F X Y') v, show T.drape _ e= _ from T.off_tree (deep T F 1 Y') v]; exact (freeze_regular T _ _ Y' b).trans (freeze_regular T _ _ Y' b).symm
lemma kept_freed (h:F=room T (univ:Finset T.Free) A m)(v:↥F): Working r A v.val.val :=by -- replace '= room .. univ' with arbitrary subset argument
 have hp: (v:T.Free) ∈ room T (univ:Finset T.Free) A m:= h ▸ v.property; have hv:= (mem_filter.mp hp).2; exact ⟨hv.1,safeIn hv (by unfold Sequest; omega)⟩
lemma beyondMake (a:Finset T.Free)(h:a⊆room T (univ:Finset T.Free) A m)(Y':LinkArray G (Blip T a))(C: LinkArray G a)(t': broken r p.threshold (T.drape (deep T a C Y')) = A) (g0:2*(r.count.val+1)<n.val) (p':suitedFee r.count.val p.threshold≤v)(s:v≤R.c) : let t:= T.drape (deep T a C Y'); let x:=fun b:↥a=> G.plog (G.mat (C b)); let f:= stock T a x; let D:=myLog T a Y' A; ProbeBox f (2*v) ∧ ProbeBox (f+D) (2*v) ∧ TrustLogs (f+D) t r A v ∧ abandon f r A m:=by
 intro t x f D
 let log_use (e:Bond n)(u:Working r A e) : G.chord (t e)≤v:= (purified p.threshold_pos.le (show _∉broken r p.threshold t from t'.symm ▸ u.1) g0 u.2).trans p'; -- parse Proof? 
 let norm_use (e:Bond n)(u:Working r A e) : ‖logX t e‖≤2*v:= (R.sleeve _ ((log_use e u).trans s)).trans (mul_le_mul_of_nonneg_left (log_use e u) (by norm_num))
 have ht (b:↥a) : Working r A b.val.val:= kept_freed (A:=A) (m:=m) rfl ⟨b.val,h b.property⟩ -- implicit tune
 have hz(e:Bond n): collect G (f+D) e= (if Working r A e then logX t e else 0):=by
    change collect G (stock T a x) e+ collect G (myLog T a Y' A) e= _; rw [myLog_field]
    by_cases G0: ∀ i:↥a,e≠i.val.val
    · rw [stock_shallow x e G0,zero_add]; have hg:logX (T.drape (deep T a 1 Y')) e=logX t e:= by unfold logX t; rw [drape_agrees (X:=C) G0] -- might rewrites left
      rw [hg]; simp [G0]
    push Not at G0; obtain ⟨i,rfl⟩:= G0; rw [if_neg (show ¬(Working r A i.val.val ∧ ∀ j:↥a,i.val.val ≠ j.val.val) from fun p=> p.2 i rfl), stock_clean, add_zero,if_pos (ht _ )]; unfold x logX t; rw [drapeX]
 have v0:0 ≤ v:= ((suitFee_pos _ p.threshold_pos).le.trans p')
 refine ⟨fun j=> ?_,fun j=> ?_,fun i u=> ?_,fun e pH=>?_⟩
 · by_cases t':∀ i:↥a,j≠i.val.val; · unfold f; rw [stock_shallow _ j t',norm_zero]; positivity
   push Not at t'; obtain ⟨b,rfl⟩:=t'; unfold f; rw [stock_clean,show x b=logX t _ from ?_]; exact norm_use b.val.val (ht b)
   unfold logX x t; rw [drapeX]
 · rw [hz]; split_ifs; rename_i he; exact norm_use _ he; rw [norm_zero]; positivity
 · exact ⟨(hz i).trans (if_pos u),log_use _ u⟩
 by_cases G0:∀ i:↥a,e≠i.val.val; · exact False.elim (pH (stock_shallow x e G0))
 push Not at G0; obtain ⟨b,rfl⟩:=G0; exact (mem_filter.mp (h b.property)).2
end YM.Gleam
#print axioms YM.Gleam.beyondMake
