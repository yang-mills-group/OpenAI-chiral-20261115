import GaugeFieldConstruction.ScreeRate
import YM.CF.Kea.Cool
import YM.CF.Flare.Coda
import GaugeFieldConstruction.WingGate
/-! # P3 similarity on exact momenta. Never set momentum 0 in cost receive phase. -/
set_option autoImplicit false
set_option maxHeartbeats 15000
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Fock.Flux
open Function Filter Metric NormedSpace Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {j:ℕ} {r C:ℝ}
variable {N:Side}

def localF (N:Side)(x:Site N):Finset (Single N):= univ.filter (fun i=> i.1.1=x)
lemma localN (x:Site N): (localF N x).card=180:=by
 let a:=localF N x; let T:SpinIdx×Slot→Single N:=fun y=>((x,y.1),y.2)
 rw [show localF N x=univ.image T from ?_,card_image_of_injective _ (show Injective T from fun i j h=> Prod.ext (congrArg (fun y:Single N=> y.1.2) h) (congrArg (fun y:Single N=> y.2) h)),card_univ,Fintype.card_prod,SU.slots]; simp [SpinIdx]
 ext ⟨⟨z,v⟩,b⟩; simp [localF,T]; tauto
lemma supported_base (q:Ket (Single N))(x:Site N)(h:∀ i,i∉localF N x → q i=0): q=∑ i∈localF N x, q i • basisKet i:=by
 nth_rw 1 [←basis_expand q]; symm; apply sum_subset (subset_univ _); intro i _ g; change q i • basisKet i=0; rw [h i g,zero_smul]
lemma support_trade (U:Site (More N) → E)(q:Ket (Single N))(x:Site N)(h:∀ i,i∉localF N x → q i=0) : let z:=acts (tradew N U).val q; ∀ i,i∉ localF N x→ z i=0:=by
 intro z i hi; unfold z; nth_rw 1 [supported_base q x h]; rw [map_sum,WithLp.ofLp_sum,Finset.sum_apply]; apply sum_eq_zero; intro j t; rw [map_smul]; simp only [WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul]; change _* ((acts _ _).ofLp i)= _; rw [basis_act]; unfold tradew; dsimp only; rw [jump_apply,if_neg ?_,mul_zero]; intro g; exact hi (mem_filter.mpr ⟨mem_univ _,(congrArg Prod.fst (show i.1=j.1 from g)).trans (mem_filter.mp t).2⟩)
lemma total_wave (A:Op (Single N))(x:Site N)(q:Ket (Single N))(u:‖q‖≤1)(f:∀ i,i∉localF N x→ q i=0)(h:∀ i∈localF N x, ‖acts A (basisKet i)‖ ≤ C): ‖acts A q‖ ≤ 180*C:=by
 nth_rw 1 [supported_base q x f]; rw [map_sum]; apply le_trans (norm_sum_le ..); refine (sum_le_sum (g:=fun _=>C) ?_).trans_eq ?_
 · intro i v; rw [map_smul,norm_smul]; exact ((mul_le_of_le_one_left (norm_nonneg _) ((PiLp.norm_apply_le q i).trans u)).trans (h i v))
 rw [sum_const,nsmul_eq_mul,localN]; norm_num

variable {I:Type*} [LinearOrder I][Fintype I]{A B P Q E : Op I}
section travel
-- letter circuits. wall transform acts preserving products. Removal needs inverse adjoint. Gauge orientation in direct input, no conjug.
abbrev translateW (P A B:Op I)(U:UNI I)(b:ℝ)(F:FC I):= wall P A U b * F * seek P B U b
def oneWarp (P A:Op I)(U:UNI I)(b:ℝ):= chips P b * A * U.val
def onePeak (P B:Op I)(U:UNI I)(b:ℝ):= star U.val * B * chips P (-b)
lemma peak_alive (V:Valve P E A B)(h:IsStarProjection P)(U:UNI I)(b:ℝ) : oneWarp P A U b * onePeak P B U b=1:=by
 unfold oneWarp onePeak; rw [show chips P b*A*U.val*(star U.val*B*chips P (-b))=chips P b*(A*((U.val*star U.val)*B))*chips P (-b) by simp only [mul_assoc],U.property.2,one_mul,V.live,mul_one,chips_ps b (-b) h,add_neg_cancel,chips_zero]
lemma awake (P A:Op I)(U:UNI I)(b:ℝ): wall P A U b =Real.exp (b*rband P) • quant (oneWarp P A U b):=by unfold wall knight oneWarp; rw [Matrix.smul_mul,Matrix.smul_mul,quant_mul,quant_mul]; rfl
lemma elevate (V:Valve P E A B)(h:IsStarProjection P)(U:UNI I)(b:ℝ)(x:Ket I): translateW P A B U b (create x) =create (acts (oneWarp P A U b) x):=by
 unfold translateW; rw [show wall P A U b*create x=create (acts (oneWarp P A U b) x)*wall P A U b from ?_,mul_assoc,wall_couple V h U b,mul_one]; rw [awake,Matrix.smul_mul,Matrix.mul_smul, quant_create]
lemma descend (V:Valve P E A B)(h:IsStarProjection P)(U:UNI I)(b:ℝ)(x:Ket I):translateW P A B U b (remove x)=remove (acts (star (onePeak P B U b)) x):=by
 let D:=wall P A U b; let T:=oneWarp P A U b; let Y:=star (onePeak P B U b); have ht: star T*Y=1:=by unfold Y; rw [←star_mul,show onePeak P B U b*T=1 from mul_eq_one_comm.mp (peak_alive V h ..),star_one]
 have he: D*remove x=remove (acts Y x) * D:=by unfold D; rw [awake,Matrix.smul_mul,Matrix.mul_smul]; congr 1; change quant T* remove x=remove (acts Y x)*quant T; rw [quant_ann,←act_mul,ht,act_one]
 change D*_*_= _; rw [he,mul_assoc, show D*seek _ _ U b=1 from wall_couple V h ..,mul_one]
lemma scale_crest (c:ℂ)(F:FC I)(P A B:Op I)(U:UNI I)(b:ℝ): translateW P A B U b (c • F)=c • translateW P A B U b F:=by unfold translateW; rw [Matrix.mul_smul,Matrix.smul_mul]
lemma translate_prod (V:Valve P E A B)(h:IsStarProjection P)(U:UNI I)(b:ℝ)(F H:FC I): translateW P A B U b (F*H)=translateW P A B U b F*translateW P A B U b H:=by
 unfold translateW; rw [show (wall P A U b * F * seek P B U b)* (wall P A U b*H*seek P B U b)=(wall P A U b*F)*(seek P B U b*wall P A U b)*H* seek P B U b by simp only [mul_assoc],couple_wall V h ..,mul_one,mul_assoc _ F H]
end travel

def PurchB (C D:ℝ) (b:ℝ)(T:Op (Single N)): Prop:= (∀ (s:Site N)(x:Ket (Single N)),‖x‖ ≤1 → (∀ i, i∉ localF N s → x i=0)→ ‖acts T x‖ ≤ D ∧ ∀ r:ℝ,0 ≤ r→ ‖acts (lowCut N r*T) x‖ ≤ C*r) ∧ ∀ r:ℝ,0 < r → ‖(1-lowCut N r)* T‖ ≤ C/r
lemma Elev (U:UNI (Single N))(p:∀ (s:Site N)(x:Ket (Single N)), (∀ i,i∉localF N s → x i=0)→ ∀ i, i∉localF N s→(acts U.val x) i=0)
 (E:Even N.val)(T:Stag N→ Op SpinIdx)(u:ScaleFunds C T)(b:ℝ) : PurchB (18000*C) (18000*C*Real.pi) b (Dofu N T*U.val):=by
 let F:= Dofu N T
 have hp(r:ℝ)(hr:0 ≤ r)(s:Site N)(x:Ket (Single N))(c:‖x‖≤1)(v:∀ i,i∉localF N s→ x i=0) : ‖acts (lowCut N r*(F*U.val)) x‖≤ 18000*C*r:=by
    rw [←mul_assoc,act_mul]; apply (total_wave _ s _ (show ‖acts U.val x‖ ≤ 1 from (act_unit_norm ..).trans_le c) (p _ _ v) (fun i _=> ScaleFunds.miss N r hr T u i)).trans_eq; ring
 refine ⟨fun s x c v=>⟨?_,fun r h=> hp r h s x c v⟩,fun r k=>?_⟩
 · have he:= hp Real.pi Real.pi_pos.le s x c v; rw [low_pi N E,one_mul] at he; exact he
 rw [←mul_assoc]; apply (norm_mul_le ..).trans; rw [show ‖U.val‖=1 from CStarRing.norm_of_mem_unitary U.property,mul_one]; refine (ScaleFunds.highPrice N _ k T u).trans ?_; gcongr; linarith only [u.1]
lemma Excite_crown (t:ℝ)(j:ℕ)(p:1≤j) : ∃ C D:ℝ,0 < C ∧0 < D∧∀ {N:Side}, Pad j N→∀ (q:Site (More N)→ SU.E)(M:Jill.Male)(b:ℝ), |b|≤ t → PurchB C D b (oneWarp (boardC N j M) (pinShift N j M) (tradew N q) b) ∧ PurchB C D b (star (onePeak (boardC N j M) (pinBack N j M) (tradew N q) b)):=by
 obtain ⟨C,g,H⟩:=move_cost t p; refine ⟨18000*C,18000*C*Real.pi,by positivity,by positivity,fun {N} v q M b h=>?_⟩
 let V:= tradew N q; let A:= oneWarp (boardC N j M) (pinShift N j M) V b; let B:= onePeak (boardC N j M) (pinBack N j M) V b
 have he:A=Dofu N (stemMove N j M b) * V.val:=by rw [← MoveV v]; rfl
 have ht:star B= Dofu N (star (stemRet N j M b)) * V.val:=by
    rw [Dofu_s, ← RetV v, show B= star V.val* bReturn N j M b by unfold B onePeak bReturn; rw [mul_assoc],star_mul,star_star]
 change PurchB _ _ _ A ∧ PurchB _ _ _ (star B); rw [he,ht]
 exact ⟨Elev V (fun x y h=> support_trade q y x h) v.1 _ ⟨g.le,fun i=> (H v.1 M b h i).1⟩ b,Elev V (fun x y h=> support_trade q y x h) v.1 _ ⟨g.le,fun i=> by rw [Pi.star_apply,norm_star]; exact (H v.1 M b h i).2⟩ b⟩
end YM.CF.Fock.Flux
end
