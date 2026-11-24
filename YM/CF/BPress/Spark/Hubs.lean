import YM.CF.BPress.Spark.Toll
/- combined cost at solver and support-wise equality. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Spark
open Function NormedSpace Finset Filter Lattice Branch Push.AbsoluteSums Grid RG Ledger MeasureTheory SU Pastry Tulip Skye Girt Scree Cube Lat Fock Vesper Spin Spin.Paint Pine Lily Pledge DoughBag --
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ContDiff Real ENNReal Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
variable {N:Side}{g h b Ω a t u:ℝ}{U: Token (Force N) N}{T: Token (LocB N) N}
open Story -- Ω bound prereq h
abbrev stampU(U:Token (Force N) N)(p:MFuel N):= U p.fst p.snd.val
abbrev stampE(T:Token (LocB N) N)(p:MReg N) := T p.fst p.snd.val
abbrev stampR:= Sum.elim (stampE T) (stampU U)
abbrev stamp (g:ℝ):= Sum.elim (fun _:WantJ N=> seedJ g) (stampR (U:=U) (T:=T))
variable {D : Type}[TopologicalSpace D]
lemma lensJ(i:WantJ N): ((LensStory N).band (.inl i)).length=(jBand i).length:=List.length_map _
lemma lensE(i:MReg N): ((LensStory N).band (.inr (.inl i))).length=i.2.val.card:=(List.length_map (as:=letter i.2.val) _).trans (length_sort ..)
lemma lensU(i:MFuel N):((LensStory N).band (.inr (.inr i))).length=i.2.val.card:=(List.length_map (as:=letter i.2.val) _).trans (length_sort ..)
abbrev highP (a g :ℝ)(B:ℕ)(e:ℝ):=hereP g a+(aPort B (2*e)+aPort B e) -- same expense reg/fuel
lemma abroad (P:Form N D)(B:ℕ)(S:Payer post0 earth T a (2*t) B)(W:Payer post1 harbor U a t B)(q:0≤g): Cash (story B) (fun i=> ahead (Saga P B) (stamp (T:=T) (U:=U) g i) i a) (δPort B) (highP a g B t):=by
 have he:= floors (horizon_j (N:=N) q S.hold B) (floors (S.bill_st (fun i=>(Wheat (redP i)).erase ∅)) (W.bill_st (fun i=>Wheat (furnaceP i)))); convert he using 1; rfl; funext i; change (stamp _ _)* a^((LensStory N).band i).length=_; rcases i with (i|(i|i)); rw [lensJ]; rfl; rw [lensE]; rfl; rw [lensU]; rfl -- tune goal equality multiple issues
variable (F:GramM N)(x: Orbit N){A: ℂ}
lemma regCard (v:RegTag F T (h:=h))(p:‖A‖ ≤1)(u:Pane N)(i:MReg N): ‖regVal F u A i‖ ≤ stampE T i:= by
 unfold regVal; rw [pickStone_val, uB,weft_u,crumb_scale,norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) p).trans (v.price ..)
lemma regEmpty(v:RegTag F T (h:=h))(p:‖A‖≤1)(u:Pane N)(i:LocB N): ‖Vesper.digit (uB F u A) i‖ ≤ T i ∅:= by
 unfold Vesper.digit; rw [uB,weft_u,crumb_scale,norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) p).trans (v.price ..)
lemma fuelCard (t:FTag F U (h:=h))(W:Force N→ℂ)(p:∀ i,‖W i‖≤1)(i:MFuel N): ‖fuelVal F x W i‖ ≤ stampU U i:=by
 unfold fuelVal pickLeaf; rw [fB,weft_u, crumb_scale,norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (p _)).trans (t.price ..)
lemma stamp_le (u:RegTag F T (h:=h))(v:FTag F U (h:=h)) (t: ‖A‖≤1)(Z:Force N→ℂ)(p:∀ i, ‖Z i‖≤1)(B R:Paint (More N))(b:MatPlan B)(r:MatPlan R)(Y:Site N→ℂ)(S:∀ i,‖Y i‖≤ g) (K:Support N)(i:Heat N): ‖issue_spin F x A Z B R Y K i‖≤ stamp (T:=T) (U:=U) g i:=by
 rcases i with (i|(i|i)); · change ‖optionW _ _ _ _ _‖ ≤ seedJ g; unfold optionW; rw [norm_mul]; exact mul_le_mul (S _) (tollT i.1 _ _ _ (r (node i.1)) (b (node i.1))) (norm_nonneg _) ((norm_nonneg _).trans (S i.1)) -- tune
 · exact regCard F u t x.1 i
 exact fuelCard F x v Z p i
-- polynomial currency eventually family 
lemma high_pos (U:1≤a)(p:0<g)(v:0≤u)(B:ℕ):0< highP a g B u:=by
 unfold highP hereP title seedJ aPort; have he:=τPort_pos; have ht:= zero_lt_one.trans_le U; positivity
lemma high_at(a:ℝ){u:ℝ→ℝ}(p:NPL u): NPL (fun x=>highP a (BPress.g x) (Pressure.radiusB x) (u x)):=by
 apply NPL.add; · let f:=fun x=>Real.exp 1 * (BPress.g x* Real.exp (Chalk.ν^2)* a^card_page* (2^card_page)); exact NPL.const_mul (((npl_g.mul (PL.const _)).mul (PL.const _)).mul (PL.const _)) _
 let h:= βPol.2.pow 4; exact NPL.add ((h.times (p.const_mul 2)).mul (PL.const _)) ((h.times p).mul (PL.const _))
end YM.CF.BPress.Spark
