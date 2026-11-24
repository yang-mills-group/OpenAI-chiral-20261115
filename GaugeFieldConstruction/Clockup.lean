/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.Stoic
import GaugeFieldConstruction.Loons
import YM.Planned.PRIMARY_INTEGRAL_295.Streets
import YM.Planned.PRIMARY_INTEGRAL_295.Savings
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Coach
/-!
# Full cover Street uses. Parent-hub pulled. L-hypotheses not hidden.
-/
set_option autoImplicit false
set_option maxHeartbeats 45000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.FlightFlux
open Function Filter Metric Lattice Wilson RG OrderedFinpartition Gauge Laurent Bloch Precision Tree Pressure Next.Free HarmP
open Planned.PrimaryIntegral295 Carrier
open scoped ContDiff Topology InnerProductSpace BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {L c f:Side}{G:Gauge}{S:StepData c f}{T: Tube G S}
variable {a b:ℝ}
-- helpers
lemma SizeS (L: Side)(n:ℕ)(x:Cover): lateral (n • x)= n*lateral x:=by simp [lateral, Finset.mul_sum, Int.natAbs_mul]
lemma cellarWalk(L:Side)(x i:Cover): cellar L (L.val • i+x)= i+cellar L x:=by
 have he:= balance L (L.val • i+x); rw [show wrap L (L.val • i+x)=wrap L x from ?_] at he; swap; · rw [map_add,joint_heads,zero_add] -- tune
 let V:= cellar L (L.val • i+x); have hh:L.val • V=L.val • (i+cellar L x):=by
    have ht:L.val • V = (L.val • i+x)-lift (wrap L x) := eq_sub_of_add_eq ((add_comm ..).trans he.symm) -- tune
    rw [ht,smul_add, show L.val • cellar L x=x-lift (wrap L x) from eq_sub_of_add_eq ((add_comm ..).trans (balance L x).symm)]; abel
 ext j; apply mul_left_cancel₀ (show (L.val:ℤ)≠0 from by positivity); have ht := congr_fun hh j; simp only [Pi.smul_apply,nsmul_eq_mul] at ht; exact ht
lemma lift_moon (x:Site L): lateral (lift x)≤ 4*L.val:=by
 have H (i : Axis) : (lift x i).natAbs ≤ L.val:=by have h:=lift_centers x i; omega
 simpa only [lateral,Finset.sum_const,nsmul_eq_mul,Axis,Fintype.card_fin, Finset.card_univ] using! Finset.sum_le_sum (s:=Finset.univ) (fun i _=> H i)
lemma wrap_month (x:Cover): pdist (wrap L x) ≤ lateral x:=by
 apply Finset.sup_le; intro i _ ; apply le_trans _ (height_l x i); -- valMinAbs minimal
 change (ZMod.valMinAbs ((x i:ℤ):ZMod L.val)).natAbs ≤ _
 by_cases hp:(L.val:ℕ)/2 ≤ (x i).natAbs; · exact (ZMod.natAbs_valMinAbs_le _).trans hp
 have hv:L.val/2 > (x i).natAbs:=lt_of_not_ge hp -- tune not_ge
 rw [show (((x i):ZMod L.val).valMinAbs)=x i from (ZMod.valMinAbs_spec ..).2 ⟨rfl,by apply And.intro <;> omega⟩]
open PhysicalNext.JointLoad
variable {P:Flight 4 4}
lemma shift_stream {σ A:ℝ}(p:0<σ)(K: Lines L)(h:K.strip σ A)(u:Window G.Color)(x d:Cover): applyLine K u (L.val • d+x)=applyLine K (fun z=> u (d+z)) x:=by
 funext i; unfold applyLine; apply Finset.sum_congr rfl; intro k _; unfold stream member; rw [map_add,joint_heads,zero_add,cellarWalk]; exact tsum_congr fun v=> by rw [add_assoc]
abbrev W_form(G:Gauge)(c:Side)(v:Directions G c)(o: Site c):Window G.Color:=fun x i=> v (o+ wrap c x,i)
-- recentered actual Locked ratio. origin o arbitrary fine. Use Streets

lemma Route_core(S:StepData c f)(T:Tube G S)(u: Next.Free.Whole T.R.A0)(F:Directions G c): W_form G f (Heir.route T F) 0 = applyLine T.R.A0 (W_form _ _ F 0):=by
 let V:=applyLine T.R.A0 (Streets.aboard G c (mapCo F)); have he:Streets.aboard G c (mapCo F)=W_form G c F 0:=by funext x i; unfold Streets.aboard; rw [map_s]; unfold W_form; rw [zero_add]
 rw [←he,← show _= applyLine T.R.A0 (Streets.aboard G c (mapCo F)) from Streets.street S.ratio _ u _]; funext i j; unfold W_form; rw [zero_add]; unfold Heir.route; rw [Heir.roll_as]; -- tune code
 rw [Streets.aboard,Exterior.collect]; rw [Streets.tagged]
 rfl
lemma Route_home(S:StepData c f)(T:Tube G S)(u:Whole T.R.A0)(F:Directions G c)(o:Site f): W_form G f (Heir.route T F) o= fun x=>applyLine T.R.A0 (W_form _ _ F (S.ratio.parent o)) (x+lift (S.ratio.residue o)):= by
 let V:= lift (S.ratio.residue o); let d:=lift (S.ratio.parent o); let L:=S.ratio.count
 funext x
 have hx: o=wrap f (L.val • d+V):=by rw [map_add, ← S.ratio.embed_wrap]; unfold V d; rw [wrap_lift]; change o=S.ratio.assemble (S.ratio.parent o,S.ratio.residue o); obtain ⟨⟨i,j⟩,hi⟩:= S.ratio.assemble_bijective.2 o; simp only [← hi,S.ratio.assemble_parent,S.ratio.assemble_res] -- tune
 have hp :W_form G f (Heir.route T F) o x= W_form G f (Heir.route T F) 0 (L.val • d+(x+V)):=by
    funext i; unfold W_form; rw [map_add,map_add,zero_add]; apply congrArg (fun x=>Heir.route T F (x,i)); nth_rw 1 [hx]; rw [map_add]; abel -- tune
 obtain ⟨σ,A,p,g⟩:= u; rw [hp, Route_core S T ⟨σ,A,p,g⟩, show _= _ from (show applyLine T.R.A0 (W_form G c F 0) (L.val • d+(x+V))=_ from shift_stream p _ g _ _ d)]; congr 2; funext i j; unfold W_form; rw [map_add,zero_add, show wrap c d=_ from wrap_lift _]
lemma Lifter (o:Site c)(v:Directions G c)(e:0≤b)(p: Heir.Limb 3 o v b): Carries (W_form _ _ v o) 3 b:=by
 refine ⟨e,fun x i=>?_⟩; apply (p (o+ wrap c x,i)).trans; unfold Heir.spine liftCost separation; dsimp only; apply mul_le_mul_of_nonneg_left _ e; apply pow_le_pow_left₀ (by positivity); gcongr; rw [add_sub_cancel_left]; exact wrap_month _ -- tune
-- up to Route energies
variable {E: Type*}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]
lemma sew_out (D:Window E)(i:Cover)(j: Axis)(x:Cover)(l:List Axis): loom l (fun x=> D (x+i) j) x=Trellis.delta D l (x+i) j:=by
 induction l generalizing x with
 | nil=> rfl
 | cons a l ih=> unfold Trellis.delta Trellis.offset; rw [loom_cons]; unfold advance; rw [ih, ih]; change Trellis.delta D l (x+step a+i) j-_= _; rw [add_right_comm]; rfl -- tune ambiguous
lemma Capac(k:ℝ)(g:0<k): ∃ D:ℝ, 1≤D∧∀ (P:Flight 4 4)(M:ℝ)(F:Window E),Carries F 3 M → ∀ (x:Site P.L)(i:Axis), Goose Dignity.norm (D* M*(P.L.val:ℝ)⁻¹*SpanL P.L) (P.L.val:ℝ)⁻¹ (fun z=> applyLine (linesOf P k) F (z+lift x) i) 3:=by
 obtain ⟨σ,C,hσ,hC,H⟩:= HarmP.hon_P (secure_both k g (j:=4) le_rfl (t:=4) le_rfl).1 1 3 le_rfl
 let D:=4*widthCost σ 3* (5:ℝ)^6 * C; have ht:0≤ widthCost σ 3:= zero_le_one.trans (widthCost_ge hσ _); have hD:0 ≤ D:=by unfold D; positivity
 refine ⟨1+D,le_add_of_nonneg_right hD,fun P M F q i a=>?_⟩; let u:= P.L; let z:ℝ:=(P.L.val:ℝ)⁻¹; have hz:0<z:=inv_pos.mpr (side_pos _); have hm:=q.1; have hL:=span_one u; unfold u at hL
 refine ⟨by change 0≤ (1+D)*M*z*_; have hp:0≤SpanL P.L:=zero_le_one.trans hL; positivity, hz.le, fun l x v=>?_⟩; rw [sew_out]
 let A:=linesOf P k; have hp(l:List Axis)(v:l.length ≤3):=H P l v
 have he (l : List Axis) (hl : l.length≤3) : Trellis.delta (applyLine A F) l=applyLine (advanceC P.L A l) F := by
    induction l with
    | nil=>rfl
    | cons a l ih=>
      rw [Trellis.delta,advanceC,ih (by simp at hl; omega)]; exact funext fun x=> Trellis.advance_step P.odd x a
        (show Whole (advanceC P.L A l) from ⟨σ,_,hσ,hp l (by simp at hl; omega)⟩) q
 let T:= C*(SpanL P.L/(P.L.val:ℝ)^(1+l.length)); let Y:=advanceC P.L A l; have hv:Y.strip σ T:=hp l v; have hw:0 ≤ T:=mul_nonneg hC.le (div_nonneg (zero_le_one.trans hL) (by positivity))
 let t:ℝ:=lateral x; have hx:0≤t:= Nat.cast_nonneg _; let Q:=1+z*t; have hQ:0≤ Q:=add_nonneg zero_le_one (mul_nonneg hz.le hx)
 change ‖Trellis.delta (applyLine A F) l (x+lift i) a‖ ≤ _; rw [he _ v]; apply ((norm_le_pi_norm ..).trans (Trellis.billed hσ hw hv q (x+lift i))).trans
 have hy:(Laurent.size (x+lift i):ℝ) ≤ t+4*(P.L.val:ℝ):=by
    let he:lateral (x+lift i)≤ lateral x+4*P.L.val:= (lateral_add ..).trans (Nat.add_le_add_left (lift_moon i) _); change (↑(lateral _):ℝ)≤(↑(lateral x):ℝ)+_; exact_mod_cast he -- tune
 have hg:1+z* Laurent.size (x+lift i) ≤ 5*Q:=by refine (add_le_add_right (mul_le_mul_of_nonneg_left hy hz.le) _).trans ?_; rw [mul_add, mul_left_comm z 4,inv_mul_cancel₀ (side_pos _).ne']; unfold Q; nlinarith
 let U:= 4*M*widthCost σ 3*(5:ℝ)^3*T; have hu:0 ≤ U:=by unfold U; positivity
 apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hg 3) hu).trans
 calc
 _ = D*M*z* SpanL P.L*z^l.length*Q^3:=by unfold U D T z; rw [div_eq_mul_inv,pow_add,mul_inv_rev, pow_one,inv_pow]; ring -- tune binder
 _ ≤ _ :=by change D*M*z* SpanL P.L*z^l.length*Q^3≤(1+D)*M*z* SpanL P.L*z^l.length*Q^3; gcongr; linarith
end YM.FlightFlux
end
