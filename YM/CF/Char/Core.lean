import YM.CF.Char.Light
set_option autoImplicit false
noncomputable section
namespace YM.CF.Char
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
local notation "φ" => S.ratio.parent
abbrev Track (c f:Side):Type:= (Signed × Site f) ⊕ Bond c
def moor(S:StepData c f): Track c f → Site c 
 | .inl (s,i)=>s.act (S.ratio.parent i)
 | .inr i=> i.1
def fOre(q:Clip)(R:PathData G)(U:Config G f)(i:Site f):ℝ:= (∑ j:PlaqAxes, (q.direct*G.price (faceValue U (i,j))+ ‖R.ell U (i,j)‖^2/2)) + (∑' j,(R.cubic j).unmasked U i) + ∑' j,(R.quartic j).unmasked U i
def chargeP(S:StepData c f)(q:Clip)(R:PathData G) (V:Config G c)(k:S.Choices)(U:Config G f): Track c f → ℝ
 | .inl (s,i) => ((Fintype.card Signed : ℝ))⁻¹ * fOre q R (pull s 0 U) i
 | .inr i => S.kernel.penalty * G.price (V i*(S.prediction U k i)⁻¹)
def alloy(T:Tube G S)(x:ℝ)(V: Config G c)(k:S.Choices)(i:Track c f)(a:Directions G f):ℝ:= chargeP S T.high (grainA T.up (Stores.till x)) V k (increment (replica S.ratio V) a) i
def rack(T:Tube G S)(x:ℝ)(V:Config G c)(k:S.Choices)(a:Directions G f):ℝ:= ∑ i:Track c f,alloy T x V k i a
lemma rack_actual(a:Directions G f) : let U:= increment (replica S.ratio V) a; rack T x V k a= mainTerm T.high (grainA T.up (Stores.till x)) U+noiseTaylor S V U k:=by
 intro U; unfold rack alloy; unfold Track; rw [Fintype.sum_sum_type,Fintype.sum_prod_type]; simp only [chargeP]
 unfold fOre mainTerm Patch.average quadratic uncut noiseTaylor; simp_rw [Fintype.sum_prod_type]; simp only [U,mul_add, Finset.sum_add_distrib, Finset.mul_sum]
lemma slot_near {U U':Config G f}{i: Site f}(a:RG.Slot)(p:a.length≤ r)(h:AgreeNear S.ratio.parent (S.ratio.parent i) (r+4) U U'): a.atSite U i=a.atSite U' i:=by
 let j:= Work.F03.slotFace a i; have he: separation (φ i) (φ j.1) ≤ a.walk.length:= slot_distance (S:=S) a i
 unfold RG.Slot.length at p
 have hh: faceValue U j=faceValue U' j:=travel_near φ (Work.E03.parent_step S) _ _ j.1 (square j.2.val.1 j.2.val.2) 4 le_rfl (h.shrink (by omega))
 rw [Work.F03.atSite_path,Work.F03.atSite_path,hh,travel_near φ (Work.E03.parent_step S) U U' i _ _ (by omega) h]
lemma oreP(q:Clip)(R:PathData G)(i:Site f)(U U':Config G f)(h:AgreeNear S.ratio.parent (φ i) (r+4) U U'):
 fOre q (grainA R r) U i=fOre q (grainA R r) U' i:=by
 let K:=grainA R r; have he (j:PlaqAxes): K.ell U (i,j)=K.ell U' (i,j):=by
    apply tsum_congr; intro u
    let s:=(R.row j u).2; dsimp only [PathData.ellTerms, K,grainA]
    split
    · rw [slot_near (R.row j u).2 ‹_› h]
    simp only [zero_smul]
 have hp {k:ℕ}(A:Atom G k): (if A.length≤r then A else dimA A).unmasked U i=(if A.length≤r then A else dimA A).unmasked U' i:=by
    split
    next hi=> exact congr_arg A.poly (funext fun l=> slot_near (A.leg l) (le_trans (show _ ≤ A.length from Finset.single_le_sum (f:=fun i=>(A.leg i).length) (fun _ _=> by omega) (Finset.mem_univ _)) hi) h)
    simp [dimU]
 have hx (j:PlaqAxes): faceValue U (i,j)=faceValue U' (i,j):= travel_near φ (Work.E03.parent_step S) _ _ i (square j.val.1 j.val.2) 4 le_rfl (h.shrink (by simp))
 change fOre q K _ _= fOre q K _ _; unfold fOre; simp_rw [hx, he]; exact congr_arg₂ _ (congr_arg (_+·) (tsum_congr fun j=>hp (R.cubic j))) (tsum_congr fun j=>hp (R.quartic j))
lemma seen(ht:S.patch.Branches S.kernel G)(i:Track c f) (h:Scan S x (moor S i) (span S.patch x) A A' F F' k k' V W Y Y') (a b:Directions G f) (he:Next.SectorChange.echo S (moor S i) (span S.patch x) a b):
 alloy T x V k i a=alloy T x W k' i b:=by
 let L:=span S.patch x; let p:= moor S i
 have hp:AgreeNear φ p L (increment (replica S.ratio V) a) (increment (replica S.ratio W) b):= fun i hi=>by unfold increment; rw [he _ hi,rep_share (S:=S) h.outer i hi]
 unfold alloy
 obtain (⟨s,i⟩|i):=i
 · rw [chargeP,chargeP, oreP _ _ i _ _ (pulled_near _ _ s _ _ (hp.shrink (by dsimp only [L,p,moor]; rw [separation_self]; unfold span; omega)))]
 rw [chargeP,chargeP, h.outer i (by change separation i.1 i.1≤_; simp)]
 have hl:= h.frames (i.1+step i.2) (show separation i.1 _ ≤ _ from (Work.E03.sep_step ..).trans (by omega))
 rw [prediction_near_eq ht _ _ k i (hp.shrink (by unfold L span p moor; rw [separation_self]; omega)), AnalyticBridge.NonflatCovarianceLocality.same_tags S i _ _ (h.frames _ (by simp [moor])) hl (h.tags _ (by simp [moor]))]
lemma selfX(V:Config G c)(k:S.Choices)(F:Forest S.ratio)(A:Stores S) : Scan S x o r A A F F k k V V (fun _=> (1:G.El)) (fun _=>1):=⟨fun _ _=> Iff.rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>Iff.rfl,fun _ _=>rfl,fun _ _ _ _=>rfl⟩
lemma alloy_same (ht:S.patch.Branches S.kernel G)(i:Track c f)(a b:Directions G f)(he: Next.SectorChange.echo S (moor S i) (span S.patch x) a b) : alloy T x V k i a=alloy T x V k i b:=
 seen ht i (selfX V k ((Tree.select S.ratio S.patch.odd_side).some) (bareStores S)) a b he
lemma echo_push (a b:Directions G f) (u:Directions G f)(he:Next.SectorChange.echo S o r a b): Next.SectorChange.echo S o r (a+u) (b+u):= fun i h=> congr_arg (·+u i) (he i h)
lemma echos (ht: S.patch.Branches S.kernel G)(h: Scan S x o r A A' F F' k k' V W Y Y')(a b:Directions G f)(he:Next.SectorChange.echo S o r a b)(u: Directions G f) (hu:∀ i: Bond f, r<separation o (φ i.1)+2*span S.patch x → u i=0) :
 rack T x V k (a+u)-rack T x V k a=rack T x W k' (b+u)-rack T x W k' b:=by
 unfold rack; rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
 refine Finset.sum_congr rfl fun i _=> ?_
 by_cases hx:separation o (moor S i)+ span S.patch x ≤ r
 · have hh:Next.SectorChange.echo S (moor S i) (span S.patch x) a b:= fun j (hj:separation (moor S i) (φ j.1) ≤ span S.patch x)=> he j ((separation_triangle ..).trans ((Nat.add_le_add_left hj _).trans hx))
   rw [seen ht i (h.shrink hx) a b hh,seen ht i (h.shrink hx) _ _ (echo_push _ _ u hh)]
 have hv(t:Directions G f): Next.SectorChange.echo S (moor S i) (span S.patch x) (t+u) t := fun j hj=>by
    have he:= separation_triangle o (φ j.1) (moor S i); rw [separation_comm (φ j.1) (moor S i)] at he
    simp only [Pi.add_apply,hu j (by omega),add_zero]
 rw [alloy_same ht i _ a (hv a), alloy_same ht i _ b (hv b), sub_self,sub_self]
end YM.CF.Char
