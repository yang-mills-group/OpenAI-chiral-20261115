import YM.CF.Peaks.Iota
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)(u v:Bool)
abbrev Inta := Site N × St G.count
def arrive (i:Inta G): Site (More P):=node ((blast G i).1)
def portico (i:Inta G) := (ratio G).embed (node i.1)
def touch (i:Inta G) := if u then arrive G i else portico G i
lemma warrant (t e): ((parcel G u e).run t).val=jump (Equiv.refl _) (fun i : Inta G=> (matter (t (touch G u i))).val):=by cases u <;> first | rfl | exact temper_form G t e
lemma peg (i:Inta G)(c:Slot)(e:ℝ): (tempo G e).home (i,c)=arrive G i:=rfl

def traceU (u:Bool){L:Side}(r:St L):Cover:= if u then 2 • lift r.1 else 0
lemma turnMap (h:Odd G.count.val)(i:Inta G): touch G u i=portico G i+wrap _ (traceU u i.2) :=by cases u; simp [touch,traceU]; exact embed_node G h i.1 i.2.1

lemma right_to (x:Site P)(w:Walk) : stop x w=x + wrap P (stop (0:Cover) w):=by nth_rw 1 [← wrap_lift x]; rw [← wrap_stop_cover, ← add_zero (lift x), stop_trans,map_add,wrap_lift]
def loopTail (i:Inta G):Walk:=route 0 (traceU true i.2-traceU u i.2) 1
lemma loopEnd (ho:Odd G.count.val) (i:Inta G): stop (touch G u i) (loopTail G u i)=arrive G i:=by rw [right_to,loopTail,route_end,map_sub,← show touch G true i=arrive G i from rfl,turnMap G true ho,turnMap G u ho]; abel
lemma tail_len(i:Inta G): (loopTail G u i).length ≤8*G.count.val:=by
  unfold loopTail; apply le_trans (route_size _ _ _ (2*G.count.val) ?_) (by omega)
  intro j; obtain hh:= lift_centers i.2.1 j; cases u
  · simp only [traceU,↓reduceIte,Pi.zero_apply,sub_zero,Pi.smul_apply,nsmul_eq_mul, Nat.cast_ofNat]; simp
    omega
  simp

def conduit (i j:Inta G)(p:Walk): Seal (Site (More P)):= traceP (touch G u i) p ∪ traceP (touch G u i) (loopTail G u i) ∪ traceP (touch G v j) (loopTail G v j)
lemma conduits (i j:Inta G)(p:Walk): (conduit G u v i j p).card ≤ p.length+16*G.count.val+3:=by
  unfold conduit; apply (card_union_le ..).trans; apply (Nat.add_le_add (card_union_le ..) (trace_k ..)).trans; apply (Nat.add_le_add_right (Nat.add_le_add (trace_k ..) (trace_k ..)) _).trans; have ht:=tail_len G u i; have he:=tail_len G v j; omega
lemma cord {p:Walk}(ho:Odd G.count.val)(i j:Inta G)(c:ℂ)(e:ℝ)(h:0<e)(he:e≤1)(hw : stop (touch G u i) p=touch G v j) :
 let S:=conduit G u v i j p; let w:=((p.length+1:ℝ)*(1+e)^p.length)*‖c‖
 Suite (badge _) (parcel G u e) (parcel G v e) S (reed i j w) (fun x=>panel i j (c • (track x.val.1 (touch G u i) p).1)):=by
  intro S w; let A:=traceP (touch G u i) p; let B:= loopTail G u i; let C:=loopTail G v j
  have hp: A⊆S:= subset_trans (subset_union_left) subset_union_left
  have ht: Grove (terr _) S := .unite (.unite (trace_g ..) (trace_g ..) (trace_source ..) (trace_source ..)) (trace_g ..) (mem_union_left (a:=touch G v j) _ (hw ▸ trace_last ..)) (trace_source ..)
  let f(y: Stem (More P)):=c • (track y (touch G u i) p).1
  have Hu:Differentiable ℂ f:=(track_d (touch G u i) p).fst.const_smul c
  let V (g : Site (More P)→E)(k:Inta G):=(matter (g (touch G u k))); let W(g:Site (More P)→ E)(k:Inta G):=matter (g (touch G v k))
  refine panel_ticket (p:=V) (q:=W) (fun g=> warrant ..) (fun g=>warrant ..) i j S w (fun x=>f x.val.1) ht (fun k=> ?_) (fun k=>?_) (fun g x=>?_) (by unfold w; positivity) ?_ ?_ (fun x=>?_) (fun x y=>?_)
  · rw [peg,← loopEnd G u ho i]; exact mem_union_left _ (mem_union_right _ (trace_last ..))
  · rw [peg,← loopEnd G v ho j]; exact mem_union_right _ (trace_last ..)
  · change (c • (track (relayg g x.val.1) (touch G u i) p).1) * (W g j).val = (V g i).val * (c • _)
    rw [track_g,hw]; change (c • ((V g i).val*_*star (W g j).val))*(W g j).val=_; rw [Matrix.smul_mul,mul_assoc _ (star (W g j).val), (W g j).property.1,mul_one, Matrix.mul_smul]
  · intro a b
    apply honors (f:=fun x:Coil N P=> f x.1 a b); exact (differentiable_pi.mp (differentiable_pi.mp (by exact Hu.comp differentiable_fst) a) b).differentiableOn
  · exact Hu.continuous.comp (continuous_fst.comp continuous_subtype_val)
  · unfold f w; rw [norm_smul,mul_comm _ ‖c‖]; refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact (norm_fst_le ..).trans ((track_size e h.le _ p _ (leftL G x.property)).trans (le_mul_of_one_le_left (by positivity) (by simp)))
  unfold f w; rw [←smul_sub,norm_smul]; rw [mul_comm _ ‖c‖,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_fst_le (track x.val.1 _ p-track y.val.1 _ p)).trans; apply (track_vol e h.le _ p _ _ (leftL G x.property) (leftL G y.property)).trans
  rw [←mul_assoc]; change _≤ _*(deal G S x.val y.val /|e|)
  apply mul_le_mul (mul_le_mul_of_nonneg_right (by simp : (p.length:ℝ)≤p.length+1) (by positivity)) _ (fare_t ..) (by positivity)
  rw [abs_of_pos h]; exact ((fare_inc hp x.val.1 y.val.1).trans (le_add_of_nonneg_right (fare_t ..))).trans (le_div_self (deal_pos ..) h he)
end YM.CF.Peaks
