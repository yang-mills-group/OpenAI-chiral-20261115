import YM.CF.Siete.Flirt
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Border
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset SU Fock Lat Spire Scroll MeasureTheory Skye Scree Cube RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset
open MultiNext.SignedSource Lyre Banjo Analysis Pressure Next.Fluctuations
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n m:Side}{k p j:ℕ}{B P:BudgetPoint}{X:Support (More n)}{o a:Seat n}{C ε u Q t:ℝ}{V:Pane n}{g:Seat n→SU.E}{r:ℕ}
structure Nut(B:BudgetPoint)(V:Pane n)(o:Seat n)(r:ℕ)(k:ℕ)(C Q t:ℝ)(g:Seat n→SU.E):Prop extends Canvas B o r V g k C where
 hC:1≤C
 hQ:C ≤ Q
 ht: loom B r C ≤ t
 hj(x:Heir.Chord group):‖x‖≤t→Through k Heir.decode x Q
 cap: B.threshold*(1+(r:ℝ))^B.power ≤1
lemma limb_cost (p:Nut B V o r k C Q t g) (v:Fin j→ tangD n)(hX:∀ i,B.dirBound o (v i))(hx:j≤k): Limb B.power o (iteratedFDeriv ℝ j (sphereQ V o r g) 0 v) (Q*B.threshold):=by
 have h:=p.toCanvas; have hP:=B.threshold_pos; have hQ:0≤ Q:=zero_le_one.trans (p.hC.trans p.hQ); intro e
 change _ ≤ Q*_ * spine _ _ _
 by_cases g':j=0; subst j; rw [iteratedFDeriv_zero_apply,sphereQ, Function.comp_apply,Work.G07.at_zero_increment]; exact (h.visible p.hC le_rfl e).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right p.hQ hP.le) (spine_pos ..).le)
 by_cases l:separation o e.1≤ r; swap; · rw [berth h e (not_le.mp l),norm_zero]; exact mul_nonneg (mul_nonneg hQ hP.le) (spine_pos ..).le
 rw [mul_assoc]; apply (post_jet h e _ _ ((h.paid p.hC).trans p.ht) p.hj l o v hX hx 0 rfl).trans; refine mul_le_mul_of_nonneg_left (pow_le_of_le_one (Lyre.width_pos ..).le ((show Lyre.width B o e ≤ _ from ?_).trans p.cap) g') hQ
 unfold Lyre.width; have ht: separation e.1 o≤ r:=by rw [separation_comm]; exact l
 gcongr
lemma step_guide(p:Nut B V o r k C Q t g): Guide _ (B.dirBound o) 0 (sphereQ V o r g) k (loom B r Q):=by
 have hP:=B.threshold_pos; have hQ:= p.hC.trans p.hQ; have hz:0≤ loom B r Q:=by unfold loom; positivity
 refine ⟨p.germ.of_le le_top,fun i hi v k=> (pi_norm_le_iff_of_nonneg hz).mpr (fun e=> ?_)⟩
 by_cases h:separation o e.1≤ r
 · have ht: separation e.1 o ≤ r:=by rw [separation_comm]; exact h
   apply (limb_cost p v k hi e).trans; unfold loom spine; gcongr
 rw [berth p.toCanvas _ (not_le.mp h), norm_zero]; exact hz
lemma title(k:ℕ):∀ C:ℝ,1≤C→∃ t Q:ℝ,0<t∧C≤ Q∧∀ {n:Side} (X:Seat n)(P:BudgetPoint)(V:Pane n)(r:ℕ)(g:Seat n→SU.E), Canvas P X r V g k C→loom P r C ≤ t→Nut P V X r k C Q t g:=by
 intro C p
 obtain ⟨K,r0,hk,hr,H⟩:= decode_cert group k
 let t:= min r0 1; refine ⟨t,max C K, lt_min hr zero_lt_one, le_max_left ..,@fun n X P V r g h hx =>⟨h,p,le_max_left ..,hx, fun x k=> ((H _ (k.trans (min_le_left ..))).1).mono (le_max_right ..),?_⟩⟩
 have ht:=P.threshold_pos; exact (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left ht.le p) (by positivity)).trans (hx.trans (min_le_right ..))
-- travel radial from healthy guard of FULL argument
open Next Next.SectorChange Precision Exterior Bloch Bid
lemma voyage {G: Gauge} (W:Heir.Web G) (x: Directions G (More n))(t:ℝ)(p:0<t)(h:Healthy (B.threshold/4) X (increment 1 x))(hw:‖x‖≤t)(hr:t≤W.radius)(ht: W.scale*t^2 ≤ B.threshold/32) (u:ℝ)(hy:u∈ Set.Icc (0:ℝ) 1): pingS B.threshold X (increment 1 (u • x)):=by
 let b:=Flat.labels x; have hf:‖b‖≤t:=(labels_area ..).trans hw; have hx:0≤u:=hy.1; have he:‖u • b‖≤t:=by rw [norm_smul,Real.norm_of_nonneg hx]; exact (mul_le_of_le_one_left (norm_nonneg _) hy.2).trans hf
 let V:=increment (1:Config G (More n)) x; let U:= increment (1:Config G (More n)) (u• x)
 classical
 intro i w; obtain ⟨y,l,g⟩:= Finset.not_disjoint_iff.mp w; let t':= W.scale*t^2
 have sy(U V:G.Color): ‖U‖ ≤ ‖V‖+‖V-U‖:=by rw [norm_sub_rev]; simpa using norm_add_le V (U-V)
 have hV: G.chord (faceValue V i) ≤ B.threshold/4:=le_of_not_gt (fun hg=> Finset.disjoint_left.mp h l ((flags_spec ..).mpr ⟨i,g,hg⟩)); let F(z:fieldDir G (More n) 1):= G.curvature (faceValue (Precision.represent z) i)
 have h': Precision.represent b = V:= labels_eq ..; have hU: Precision.represent (u • b)=U:= labels_eq (u • x)
 let L(z:fieldDir G (More n) 1):= Work.F03.faceCurl i z
 have hg:‖L b‖≤ B.threshold/4 +t':=by
    have hx:= (W.defect _ i (hf.trans hr)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hf _) (zero_le_one.trans W.cost)); refine (sy (L b) (F b)).trans (add_le_add ?_ hx); unfold F; rw [h']; exact (G.curvature_norm _).trans hV
 have heq:L (u • b)=u • L b:=by unfold L Work.F03.faceCurl; ext j; exact congr_fun (Matrix.mulVec_smul (Exterior.d 1 (More n)) u (parts G 1 b j)) (i.1, Exterior.plaquette i.2)
 have hQ:= W.travel _ i (he.trans hr)
 have hy:‖F (u • b)‖≤ B.threshold/4+t'+t':=by
    refine (sy (F (u • b)) (L (u • b))).trans (add_le_add ?_ ?_) -- quotes refine
    · rw [heq,norm_smul,Real.norm_of_nonneg hx]; exact (mul_le_of_le_one_left (norm_nonneg _) hy.2).trans hg
    rw [norm_sub_rev]; exact (W.defect _ i (he.trans hr)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) he _) (zero_le_one.trans W.cost))
 change G.chord (faceValue U i) < B.threshold; rw [←hU]; apply hQ.trans_lt; change 2*‖F _‖< _; change t'≤ _ at ht; linarith only [hy,ht,B.threshold_pos]
end YM.CF.Siete
