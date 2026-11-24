import ForceSatin.Echelon
import YM.SU5.Circuit.Borealis
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Circuit.SpringDay
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Onyx CF.Fir
open Precision Exterior RG Work.F06
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix
local notation "π" => Real.pi

lemma Temper (F:Momentum→ℂ)(p:Differentiable ℂ F) (ι:Type*):Moderate (fun _:ι=>1) fun _=> F:=by
 obtain ⟨A,a⟩:= (isCompact_closedBall (0:Momentum) domainRadius).bddAbove_image p.continuous.norm.continuousOn
 refine ⟨zone,max A 1,zone_pos,lt_max_of_lt_right one_pos,fun i=> ⟨fun y _=>p y,fun y c=>?_⟩⟩
 rw [mul_one]; exact (a ⟨y,mem_closedBall_zero_iff.mpr ((pi_norm_le_iff_of_nonneg domainRadius_pos.le).mpr fun i=> zone_in_disk _ c i),rfl⟩).trans (le_max_left ..)
@[fun_prop] lemma blueR : ContDiff ℝ ∞ Complex.ofReal := Complex.ofRealCLM.contDiff
namespace Lyra
variable {ι:Type*}(T:Lyra ι)
-- universal stencil cost across patches, any order designated directions.
def threadV (v:Cover)(p:Momentum):ℂ:=mode p v-1
@[fun_prop] lemma along_s (v:Cover): Differentiable ℂ (threadV v):=by unfold threadV mode; fun_prop
@[fun_prop] lemma thread_s (v:Cover): ContDiff ℝ ∞ (threadV v ∘ tmap):= by unfold threadV mode; unfold Function.comp tmap; fun_prop
lemma soar (v:Cover)(a:Axis):Act T.Hint 1 fun i z=> threadV v (T.amber a i z):= (T.amethyst a).freeze (Temper _ (along_s v) _) (fun _=>by simp [threadV,mode])
lemma soul_sub(i:Cover){x y:Bin}(p:peers x y):threadV i (tmap x)=threadV i (tmap y):=by obtain ⟨v,rfl⟩:=p; rw [map_stem]; unfold threadV; rw [mode_phase,mode_periodic,mul_one]
namespace Singer
variable {T}{V:ι→Momentum→ℂ}{W:Momentum→ℂ}{m:ℕ}(S:Singer T m V W)
include S
lemma forward (v:Cover): Singer T (m+1) (fun i z=> threadV v z * V i z) (fun z=>threadV v z*W z):=by
 refine ⟨fun a=>?_,fun a=>?_,fun x h=> ((thread_s v).contDiffAt.mul (S.rate x h)),fun i=>by rw [S.summit],fun x y i p q u=>?_⟩ -- tune *
 · have ht: (↑(m+1):ℤ)-1=1+(↑m-1):=by omega
   exact ht ▸ ((T.soar v a).mul (S.Act a))
 · have he:= (T.soar v a).mul (S.bill a); simp only [←mul_sub]; rw [Nat.cast_add,Nat.cast_one,_root_.add_comm]; exact he
 rw [S.peers x y i p q u,soul_sub v p]
end Singer
noncomputable abbrev condense (l:List Cover)(x:Momentum):ℂ:= (l.map (fun i=>threadV i x)).prod
variable {T V W m}
lemma Bouquet (S:Singer T m V W)(l:List Cover):Singer T (m+l.length) (fun i p=> condense l p * V i p) (fun p=>condense l p *W p):=by
 induction l with
 | nil=> simpa [condense] using S
 | cons i l y=> have he:=y.forward i; simpa only [condense,List.map_cons,List.prod_cons,List.length_cons,←_root_.add_assoc, _root_.mul_assoc] using he
end Lyra

-- continuum Taylor symbols and tax through actual shifts
abbrev Fain (p:Momentum):=prodM p p
abbrev Vaunt (p:Momentum):= Complex.exp (-Fain p)
lemma cairn(p:Bin):‖p‖^2 ≤ ‖Fain (tmap p)‖:=by
 have hp:=abut p; rw [Fain,prodM_self (tmap p) (tmap_physical _), Complex.norm_real,Real.norm_of_nonneg (sum_nonneg (fun _ _=>sq_nonneg _))]; apply hp.trans_eq; apply sum_congr rfl; intro i _; unfold tmap; simp -- tune sphere
section
variable {ι:Type*}{t:Tax ι}{p:ι→ℂ→Momentum}(H:Move t p)
include H
lemma poplin: Act t 0 fun i z=> Vaunt (p i z):= H.plunge (Temper _ (by unfold Vaunt Fain prodM; fun_prop : Differentiable ℂ Vaunt) _)
lemma falcon : Act t 1 fun i z=>1 - Vaunt (p i z):= H.freeze (Temper (1-Vaunt) (by unfold Vaunt Fain prodM; fun_prop) _) (fun i=>by simp [Vaunt,Fain,prodM])
-- compare shell of cliff: metric enough before zeros paid
lemma signify (x:Axis):Act t 2 fun i z=> tripQ 1 (p i z) x - Complex.I*((p i z) x):=by
 let V(p:Momentum):= tripQ 1 p x - Complex.I*p x
 apply (H.daze (Temper _ (by unfold V tripQ chip; fun_prop : Differentiable ℂ V) _) (fun i=> by simp [V,tripQ,chip]) (fun i p=>?_))
 simp only [V,tripQ,chip, Pi.smul_apply,smul_eq_mul]; have h:=((hasDerivAt_id' (0:ℂ)).mul_const (p x)).const_mul Complex.I
 have hh:= h.cexp.sub_const 1; simpa using! hh.sub h
end
-- basis ContDiff
@[fun_prop] lemma tmap_c:ContDiff ℝ ∞ tmap:= by unfold tmap; fun_prop
@[fun_prop] lemma fain_c:ContDiff ℝ ∞ (Fain ∘ tmap):=by unfold Fain prodM tmap Function.comp; fun_prop
lemma raised (p:Bin)(h:p≠0):ContDiffAt ℝ ∞ (fun x:Bin=> (Fain (tmap x))⁻¹) p:= fain_c.contDiffAt.inv (show Fain (tmap p)≠0 from norm_pos_iff.mp (lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr h) _) (cairn p)))
#print axioms falcon
end YM.Regis.Circuit.SpringDay
namespace YM.Regis.Circuit.SpringDay
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Onyx CF.Fir
open Precision Exterior RG Work.F06
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix

-- canonical Spin flat torus price (before H transpose/amplification factors)
abbrev imp (a:Axis)(L:Male)(p:Momentum):ℂ:= skin 4 L.val p a *(shell 4 L.val p)⁻¹
abbrev incense (a:Axis)(p:Momentum):ℂ:= Vaunt p*(2*p a*(Fain p)⁻¹)
lemma amber_dot{ι:Type*}(T:Lyra ι)(x:Axis)(i:T.Herb): T.amber x i 0=tmap i.go:=by simp [Lyra.amber,raf,spark]
lemma emblem{ι:Type*}(T:Lyra ι)(x:Axis)(i:T.Herb): 1* (T.Hint.r i)^(2:ℤ)≤ ‖Fain (T.amber x i 0)‖:=by rw [one_mul,amber_dot,zpow_ofNat]; exact cairn i.go
lemma magnum {ι:Type*}(T:Lyra ι)(M:ι→Male)(a:Axis): T.Singer 0 (fun i=> imp a (M i)) (incense a):=by
 have he (x:Axis): Act T.Hint (-1) (fun i z=> imp a (M i.era) (T.amber x i z)) ∧ Act T.Hint 0 (fun i z=> imp a (M i.era) (T.amber x i z)-incense a (T.amber x i z)):=by
    let W:=T.Hint; let P:= T.amber x; let m(i:T.Herb):=(M i.era).val; have hz(i:T.Herb): Odd (m i).val:= (M i.era).property
    let v(i:T.Herb)(z):=skin 4 (m i) (P i z) a; let f(i:T.Herb)(z:ℂ):= shell 4 (m i) (P i z); let U(i:T.Herb)(z:ℂ):= (1/4:ℂ)* Fain (P i z); let p(i:T.Herb)(z:ℂ):=(1/2:ℂ)*P i z a; let G:= T.amethyst x
    have hV: Act W 2 f:= G.glass m hz 4 (by decide); have hp: Act W 2 U:= G.knot.lit _; have ht: Act W 1 p:= (G.oneA a).lit _; have hv:Act W 2 fun i z=> v i z-p i z:= G.coldS m hz 4 (by decide) a
    obtain ⟨w,r,d⟩:= court 4 (by decide) (fun i:T.Herb=> M i.era) (t:=W) (fun i=>i.go) (fun _=>rfl) (fun i=>i.cap); have hh(i:T.Herb): w* (W.r i)^(2:ℤ)≤ ‖f i 0‖:=by unfold f P; rw [amber_dot,zpow_ofNat]; exact d i
    have he (i:T.Herb): (1/4:ℝ)*(W.r i)^(2:ℤ) ≤ ‖U i 0‖:=by unfold U P; have hv:= emblem T x i; rw [one_mul] at hv; rw [norm_mul]; norm_num; gcongr
    have hx:= hV.inv ⟨w,r,hh⟩; have hu:= hp.inv ⟨1/4,by norm_num,he⟩; have h:= Act.inv_gap hV hp (G.quartz m hz 4 (by decide)) r (by norm_num : 0< (1/4:ℝ)) hh he
    have hi: Act W 1 v:= by have h:Act W 1 _:= (hv.loose (by decide : (1:ℤ)≤2)).add ht; simp only [sub_add_cancel] at h; exact h
    have e:Act W 0 (fun i z=>v i z * (f i z)⁻¹-p i z*(U i z)⁻¹):= Act.diffM (a:=1) (p:=1) (q:=-2) ht hx hv h
    refine ⟨hi.mul hx, ?_⟩
    convert e.add ((falcon G).mul (ht.mul hu)) using 1; ext1 i; ext1 z; simp only [incense,U,P,v,m,p,mul_inv, f,imp] -- tune
    norm_num; ring -- tune
 refine ⟨fun x=>(he x).1,fun x=>(he x).2,fun x h=> ?_,fun i=>?_,fun x y i p t v=>?_⟩
 · apply ContDiffAt.mul; exact (Complex.contDiff_exp.comp fain_c.neg).contDiffAt
   exact ((contDiffAt_const.mul (show ContDiffAt ℝ ∞ (fun p:Bin=> tmap p a) x from (show ContDiff ℝ ∞ (fun p:Bin => tmap p a) by unfold tmap; fun_prop).contDiffAt)).mul (raised _ h)) -- tune
 · unfold imp incense; rw [show shell 4 (M i).val 0=0 from (by simp)]; simp
 unfold imp; obtain ⟨w,rfl⟩:=p; rw [map_stem] at *; rw [show skin 4 (M i).val _ a= _ from skin_overlap _ _ _ _ t w v,shell_overlap _ _ _ t w v] -- tune
#print axioms magnum
end YM.Regis.Circuit.SpringDay
