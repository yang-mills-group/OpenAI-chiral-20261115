import YM.SU5.LitCurrent.Bloom
-- adaptation of Bloom & Coil
import YM.SU5.SatinWard.Resolution.DegreePath
import YM.SU5.SatinWard.Resolution.Spark
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "I" => Single N
open Buffered _root_.Zephyr.Chern
variable {B W:ℝ}

open IndexMag Chamber Surplus
abbrev btraceF {P T:SOp N}(D:Division)(E:Pattern P T r d a v)(x:Site N)(K:Scree.Loom N)(p:BudgetPoint)(k:ℕ) : ℝ→ℂ := Surplus.btax K p D x k E ∘ turntable N
abbrev btracer (D:Division)(P:SOp N)(r:ℕ)(x:Cover)(t:ℝ):ℂ:= Matrix.trace ((P (profile (turntable N t))-tickA N)* hall D (roomW (wrap N x) r))
lemma bmaskedBloom {P T:SOp N}(D:Division)(pP:Solo a b P d)(E:Pattern P T r d a v)(x:Cover){K:Scree.Loom N}{t:ℝ}{p:BudgetPoint}{k q:ℕ}
    (z:Checked p K t d a k q) (w:Oily a d (breadth x) W) : Bud (btraceF D E (wrap N x) K p k) ∧
    ∀ i:Fin 3,
      ‖bud (btracer D P r x) i-bud (btraceF D E (wrap N x) K p k) i‖≤ W*(Real.exp (-a*k)*expiry (4*a) v):=by
 let X:=stream N; let W₀:=wrap N x; let A:= grantA D E W₀; let g(t):=Matrix.trace (beforePing A k (profile (petals X t))); let f(t):=Matrix.trace (beyond A k (profile (petals X t)))
 let u:= totals A z.hint (E.moorA _) k
 obtain ⟨h₀,_⟩:= paid_site_card (beforePing A k) u.1.pay X w (deep_grace x)
 obtain ⟨h₁,r'⟩:= paid_site_card (beyond A k) u.2 X w (deep_grace x)
 have h:Bud f:=h₁; have H:Bloom g (bud g):= Bud.bloom h₀
 have hp:(btraceF D E (wrap N x) K p k) =ᶠ[𝓝 0] g:=by
    filter_upwards [petal_on p (offsetMask p.B W₀) X,petals_open z.angle X] with t v e
    let U:=petals X t; let V:Orbit N:=(U,Classical.arbitrary _); let y:Openc (More N) d:=⟨profile U,e⟩
    change Matrix.trace (live K p k W₀ A V.1)=Matrix.trace (beforePing A k y.val); rw [noTag W₀ A z (E.moorA _),if_pos v]; exact congrArg Matrix.trace (runs W₀ A z (E.moorA _) V v U y rfl (fun _ _ _ _ _ _ _ _=>rfl))
 have ht:btracer D P r x =ᶠ[𝓝 0] (fun t=>g t +f t):=by
    filter_upwards [petals_safe X z.angle, petals_open z.angle X] with t h₀ h₁
    let U:=petals X t; let Y:= (⟨profile U,h₁⟩:Openc (More N) d)
    change Matrix.trace ((P Y.val-tickA N)* hall D (roomW W₀ r))=Matrix.trace (beforePing A k Y.val)+Matrix.trace (beyond A k Y.val)
    rw [← shadows D W₀ E Y U h₀ rfl pP r rfl, ← Matrix.trace_add,saw_recover]; -- tune
 refine ⟨(H.congr hp).1, fun i=>?_⟩; rw [((H.add h.bloom).congr ht|>.bud_eq), (H.congr hp|>.bud_eq),Pi.add_apply, add_sub_cancel_left]; exact r' _
lemma stair_length {B':ℕ} (G:Cover→List Cover)(h:∀ x,(G x).length=B') (x:Cover)(i:Axis)(r:ℕ) : (stair G i x r).length=4*r*B':=by
 induction r with|zero=> simp [stair]|succ r p=>simp only [stair,List.length_append,p,h]; rw [mul_add,add_mul]; omega
lemma layout_length (x:Cover)(l:List Axis): (layout r x l).length=(4*r)^l.length:=by
 induction l generalizing x with|nil=>simp[layout]|cons i l p=> simp only [layout,List.length_cons]; rw [stair_length _ p,pow_succ,mul_comm (4*r)]
abbrev bmass (r:ℕ):ℕ:= (4*r)^4
lemma layout_mass (x:Cover) : (layout r x arcOrder).length=bmass r:=layout_length x arcOrder
variable (D:Division)
local notation "F" => markG D N
private lemma trace_hall (p q:Op I): Matrix.trace (p * hall D q)=Matrix.trace (hall D p * q):=by
 unfold hall; simp only [← mul_assoc]; rw [Matrix.trace_mul_comm _ F]; simp only [mul_assoc]
lemma trace_house (p:Op I)(x:Cover): Matrix.trace (p * hall D (houseW (wrap N x)))= site_root N x D p :=by
 rw [trace_hall,house_trace,← sub_sum D (f:=fun i=> hall D p (chTag N x i) (chTag N x i))]; apply sum_congr rfl; intro i _; rw [hallAt]; exact if_pos ⟨mem_filter.mpr ⟨mem_univ _,(show SU.charge i.2.val∈D from (mem_filter.mp i.2.property).2)⟩,mem_filter.mpr ⟨mem_univ _,(show SU.charge i.2.val∈D from (mem_filter.mp i.2.property).2)⟩⟩ -- syntax
 intro i hi; rw [hallAt]; simp [fortune,chTag,_root_.Zephyr.Chern.tag, existsSlot, hi]
noncomputable abbrev blevel (P:SOp N)(x:Cover)(t:ℝ):ℂ:= Matrix.trace ((P (profile (turntable N t))-tickA N)*hall D (houseW (wrap N x)))
lemma bcalc (x:Cover)(r:ℕ)(P:SOp N)(t:ℝ):btracer D P r x t=((layout r x arcOrder).map fun y=> blevel D P y t).sum:=by
 unfold btracer; rw [←layout_eq]; generalize layout r x arcOrder = l; induction l with|nil=>simp [hall]| cons i t h=> simp only [List.map_cons,List.sum_cons,hallPlus,mul_add,Matrix.trace_add,h]
lemma bfund (P:SOp N)(x:Cover)(p: Solo a b P d) (h:0<d) : Bud (blevel D P x) ∧ bud (blevel D P x) 2=bud (harvest P D x (stream N)) 2:= by
 let f:= harvest P D x (stream N); let y:= -Matrix.trace (tickA N * hall D (houseW (wrap N x)))
 rw [show blevel D P x = (fun t=>f t+y) from funext fun i=>by rw [blevel,sub_mul,Matrix.trace_sub, trace_house]; rfl]; let h:= ((section_bill D p h (stream _) x).1.bloom).add (_root_.Zephyr.Chern.Bloom.constant y); exact ⟨h.1,by rw [h.bud_eq,Pi.add_apply]; exact add_zero _⟩
lemma bcounter {P T:SOp N}(pP:Solo a b P d)(E:Pattern P T r d a v)(x:Cover){K:Scree.Loom N}{t ε:ℝ}{p:BudgetPoint}{k q:ℕ}
    (z:Checked p K t d a k q) (w:Oily a d (breadth x) W) (u:∀ i∈layout r x arcOrder, ‖bud (harvest P D i (stream N)) 2-medalD D‖ ≤ ε) : Bud (btraceF D E (wrap N x) K p k) ∧
    ‖bud (btraceF D E (wrap N x) K p k) 2 - bmass r * medalD D‖ ≤ (bmass r)*ε+W*(Real.exp (-a*k)*expiry (4*a) v):=by
 obtain ⟨g,e⟩:= bmaskedBloom D pP E x z w; refine ⟨g,(norm_sub_le_norm_sub_add_norm_sub _ (bud (btracer D P r x) 2) _).trans ?_⟩
 rw [norm_sub_rev (bud (btraceF D E (wrap N x) K p k) 2),add_comm (↑(bmass _) * ε)]; refine add_le_add (e 2) ?_
 let V(l:List Cover)(t:ℝ):ℂ:= (l.map (fun i=> blevel D P i t)).sum
 let C:=medalD D
 have he(l:List Cover)(p:∀ i∈l, ‖bud (harvest P D i (stream N)) 2-C‖ ≤ ε): Bud (V l) ∧ ‖bud (V l) 2-l.length*C‖ ≤ l.length*ε:= by
    induction l with
    | nil => rw [show V []=(fun _=>0) from rfl]; have hv:=_root_.Zephyr.Chern.Bloom.constant 0; refine ⟨hv.1,?_⟩; rw [hv.bud_eq]; simp
    | cons i l ih =>
         obtain ⟨h,r'⟩:= bfund D P i pP z.angle; obtain ⟨q,hq⟩:=ih (fun j t=>p j (List.mem_cons_of_mem _ t)); let u' := h.bloom.add q.bloom; rw [show V (i::l)= (fun t=> blevel D P i t + V l t) from funext fun t=> by simp[V]]
         refine ⟨u'.1,?_⟩; simp only [u'.bud_eq,Pi.add_apply]; rw [r',List.length_cons]; push_cast; refine le_trans (le_of_eq (congrArg norm (show _=(bud (harvest P D i (stream N)) 2-C)+(bud (V l) 2-l.length*C) from by ring))) ((norm_add_le ..).trans ((add_le_add (p i List.mem_cons_self) hq).trans_eq (by ring)))
 rw [show btracer D P r x=V (layout r x arcOrder) from funext fun t=> bcalc D x r P t,←layout_mass x]; exact (he _ u).2

lemma dept_wont (r:ℕ)(j:ℕ)(t:1≤j)(D:Division)(x:Cover)(ε:ℝ)(p:0<ε):∃ v:ℕ,∀ {N:Side}, v ≤ N.val → ∀ m:Tulip.Male,∀ i∈ layout r x arcOrder, ‖bud (harvest (funde j m N) D i (stream N)) 2-medalD D‖ ≤ ε :=by -- scope
 choose v h using fun x=> polarTest D t x ε p; let u:=(layout r x arcOrder).toFinset; refine ⟨u.sup v,fun {N} p m i hp=>(h i ?_ m).le⟩; exact le_trans (le_sup (List.mem_toFinset.mpr hp)) p
#print axioms bcounter
#print axioms dept_wont
end YM.CF.LitCurrent
