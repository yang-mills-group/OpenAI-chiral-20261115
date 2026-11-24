import YM.SU5.Exchange.Pilot.Bundle
import YM.SU5.Exchange.Pipe.Raw
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v s t:ℝ}{l q:ℕ}{p:BudgetPoint}
local notation "Ω"=> Single N
-- exposure request all flag consultations on actual Budget.Ap.Use billed soak with less SUCH energy. center enlargement P.B times l
abbrev reefCost(l:ℕ)(p:BudgetPoint)(s h:ℝ):ℝ:= (p.order+1:ℝ)*h^2*Real.exp (s*Fief.tileN l)
abbrev grooveB(l:ℕ)(p:BudgetPoint)(o:Seat N):Sa N:=halo (l*p.B) {o}
structure DockPulse(p:BudgetPoint)(K:Scree.Loom N)(t d a h s:ℝ)(l q:ℕ): Prop where
    hint: 0 < a
    high: 1 ≤ h
    pos:0 < d
    roof: Roof N t d q K
    reach: p.threshold ≤ t
    hood:0 ≤ s
    room: ∃ v u:ℝ,HopeT d v u p.order ∧ p.threshold ≤ u
    width:q+10 ≤ l*p.B
    most:3 ≤ p.B
    fees:cipherK q ≤ 5*p.B
    goal:2*s*Fief.tileN l≤a*(p.B:ℝ)
variable {u h:ℝ}{K:Scree.Loom N}(T:DockPulse p K t d a h s l q)
-- receipt with Birth property.True captures zero-H terms upon tilt.R.Sol
structure Plasma (p:BudgetPoint)(q:ℕ)(D:Sa N)(h s:ℝ)(Z:Firing N)(v b:ℝ): Prop where
    ticket: ∃ W:Bag N, Barrage p q D h W s v b ∧ Z=giveB W
namespace Plasma
variable {Z W:Firing N}{D:Sa N}{r:ℝ}
lemma arc (f:Plasma p q D h s Z v b)(t:Plasma p q D h s W u r): Plasma p q D h s (Z+W) (v+u) (b+r):=by
 obtain ⟨X,H,x⟩:=f.ticket; obtain ⟨Y,F,y⟩:=t.ticket; exact ⟨_,H.plusR F,by rw [x,y]; simp only [giveB,Pi.add_apply,sum_add_distrib]⟩
lemma scale (f:Plasma p q D h s Z v b)(c:ℂ):Plasma p q D h s (c • Z) (‖c‖*v) (‖c‖*b):=by
 obtain ⟨X,H,x⟩:=f.ticket; exact ⟨_,H.swell c,by rw [x]; simp only [giveB,Pi.smul_apply,smul_sum]⟩
lemma minus (f:Plasma p q D h s Z v b): Plasma p q D h s (-Z) v b:=by simpa only [neg_one_smul,norm_neg,norm_one,one_mul] using f.scale (-1)
lemma dropW (f:Plasma p q D h s Z v b)(g:v ≤ u)(z:b ≤ r):Plasma p q D h s Z u r:=by
 obtain ⟨X,H,x⟩:=f.ticket; exact ⟨_,H.bigR g z,x⟩
lemma null : Plasma p q D h s 0 0 0:=⟨0,Barrage.zeroR,by simp [giveB]⟩
lemma subW (f:Plasma p q D h s Z v b)(t:Plasma p q D h s W u r): Plasma p q D h s (Z-W) (v+u) (b+r):=by rw [sub_eq_add_neg]; exact f.arc t.minus
lemma preens {ι:Type*}(S:Finset ι)(F:ι→ Firing N)(U V:ι→ℝ)(x:∀ i∈ S,Plasma p q D h s (F i) (U i) (V i)): Plasma p q D h s (∑ i∈ S,F i) (∑ i∈ S,U i) (∑ i∈ S,V i):=by
 induction S using Finset.induction_on with
 |empty=> rw [sum_empty,sum_empty,sum_empty]; exact Plasma.null
 |insert i S v ih=> rw [sum_insert v,sum_insert v,sum_insert v]; exact (x i (mem_insert_self ..)).arc (ih (fun i p=>x i (mem_insert_of_mem p)))
lemma mask (f:Plasma p q D h s Z v b)(P:Sa N)(e:P⊆ D): Plasma p q D h s (capR p P Z) v b:=by
 obtain ⟨X,H,x⟩:= f.ticket; refine ⟨_,H.fresh P e,?_⟩; rw [x]; funext U; unfold giveB; rw [Finset.sum_apply]; by_cases v:U∈ pingMask p P
 · rw [capR,Set.indicator_of_mem v,Finset.sum_apply]; simp only [capR,Set.indicator_of_mem v]
 rw [capR, Set.indicator_of_notMem v]; simp_rw [capR,Set.indicator_of_notMem v]; simp
-- Failure branch (if using a partially unmasked estimate) ONLY needs FLAG charges. No-zero on mask.Flight.
lemma unmask (f:Plasma p q D h s Z v b)(P:Sa N)(e:P⊆ D) : Plasma p q D h s (Z-capR p P Z) (v+v) 0:=by
 obtain ⟨X,H,x⟩:= f.ticket; obtain ⟨Q,J,w,U,hq,he⟩:= H.price
 let A: Bag N:=fun i=> X i-capR p P (X i)
 have hp: Barrage p q D h A s (v+v) 0:=by
    have hx(i:Aura N)(p':¬D⊆ i.val): A i=0:=by
       unfold A; rw [(U i p').1,capR,show (pingMask p P).indicator (0:Firing N)= (0:Firing N) from Set.indicator_zero .. , sub_self] -- tune
    refine ⟨Q+Q,0,fun i=>?_ ,fun i p'=>⟨hx i p',by rw [Pi.add_apply,(U i p').2.1,zero_add],rfl⟩,by rw [voyage_plus]; exact add_le_add hq hq,by simp [voyageB]⟩
    by_cases g:D ⊆ i.val; swap; · change Flight p q i h (A i) (Q i+Q i) 0; rw [hx i g,(U i g).2.1,zero_add]; exact Flight.zeroR
    apply Flight.laidR; · unfold A; rw [sub_eq_add_neg]; exact (w i).tube.addR (((w i).tube.mask P (e.trans g)).negR)
    intro Y u V v; have ht:V∈pingMask p P:=(pingFix (e.trans (g.trans u)) v).mpr (by simp)
    unfold A; rw [Pi.sub_apply, capR, Set.indicator_of_mem ht,sub_self,act_zero]
 refine ⟨A,hp,?_⟩; rw [x]; funext j; unfold giveB A; rw [Finset.sum_sub_distrib,Pi.sub_apply,Pi.sub_apply]; apply congrArg
 unfold capR; rw [Finset.sum_apply]; by_cases u:j∈pingMask p P
 · rw [Set.indicator_of_mem u,Finset.sum_apply]; simp_rw [Set.indicator_of_mem u]
 rw [Set.indicator_of_notMem u]; simp_rw [Set.indicator_of_notMem u]; simp
end Plasma
local notation "Σk"=> grooveB l p o
local notation "U🌐"=> roller T.pos T.roof
variable (r:Bool)(iQ:SOp N)(f:Soak o iQ a v d)(J:Op (Single N)→ FC (Dwell N))(Z:Single N→Single N→FC (Dwell N))(P0: Glyph J Z h)
include T f P0
lemma Mortgage (hp:r=false →∀ F:Op Ω, acts (J F) (vacuum (Dwell N))=0) : let W:= reefCost l p s h*v; Plasma p q Σk h s (fun x=> J (iQ (roller T.pos T.roof x).val)) W (if r then W else 0):=by
 intro U; obtain ⟨F,W₀,t,u,z,w⟩:= f; obtain ⟨A,B,hE,hV⟩:=T.room
 let P':= univ.filter fun S:Sa N=>W₀ S ≠0; let ΛZ:= grooveB l p o
 let Y(S:Sa N):= halo (l*p.B) S; let V(V_:Sa N): Aura N:= if p:V_∈P' then ⟨Y V_, o,halo_subset _ V_ (show o∈ V_ from Classical.not_not.mp (mt (u V_) (mem_filter.mp p).2))⟩ else ⟨{o},singleton_nonempty _⟩
 have hx(S)(p:S∈P'):(V S).val=Y S:=by unfold V; rw [dif_pos p]
 let F'(S:Sa N): Firing N:= Glyph.cure J T.roof T.pos (F S); let X(S):= fun i:Aura N=> if i=V S then F' S else (0:Firing N); let R(S:Sa N):=Glyph.vest p h (W₀ S); let v(S:Sa N):=R S * tact s p.B (V S); let V0(S:Sa N):= if r then v S else 0
 have hz(S)(s:S∈P') :Flight p q (V S) h (F' S) (R S) (if r then R S else 0):=by
    -- important: passes ACTUAL Loom even if paths pivot. Sector & rank on cert apertures only
    have hu:halo (q+10) S⊆ (V S).val := (hx S s).symm ▸ Corona.halo_mono T.width le_rfl; have h:=Herb.kernelR T.roof T.pos J Z (t S) P0 T.reach hE hV T.fees T.most hu
    split; exact Flight.once h; next hb=> exact Flight.laidR h fun _ _ _ _=> hp (by simpa using hb) _
 let X':=∑ S∈ P', X S
 have h0(S)(fH:S∈P') :Barrage p q ΛZ h (X S) s (v S) (V0 S):=by
    have Hp:ΛZ⊆ (V S).val:=by rw [hx S fH]; exact Corona.halo_mono le_rfl (singleton_subset_iff.mpr (Classical.not_not.mp (mt (u S) (mem_filter.mp fH).2)))
    have hv := Barrage.single (s:=s) (V S) (F' S) (hz S fH) Hp
    unfold V0 v; split <;> rename_i g; · rw [if_pos g] at hv; exact hv
    rw [if_neg g,zero_mul] at hv; exact hv
 have he := Barrage.whole P' X v V0 h0
 have htJ:(∑ S∈P',v S) ≤ U:=by
    apply le_trans _ (mul_le_mul_of_nonneg_left z (show 0 ≤reefCost l p s h from by unfold reefCost; positivity))
    rw [mul_sum]; refine le_trans (b:=∑ i∈P',reefCost l p s h * (Branch.rent a i * ledgerV (W₀ i))) (sum_le_sum fun i hi=> ?_) (sum_le_sum_of_subset_of_nonneg (subset_univ P') (fun i _ _=> ?_)) -- order holes
    · unfold v R Glyph.vest; refine le_trans (mul_le_mul_of_nonneg_left ?_ (show 0 ≤ ((p.order+1:ℝ)*ledgerV (W₀ i)*h^2) from mul_nonneg (mul_nonneg (by positivity) (sum_nonneg fun j _=>sum_nonneg fun k _=> (t i).nonn j k)) (by positivity))) (b:= (p.order+1:ℝ)*ledgerV (W₀ i)*h^2* (Real.exp (s*Fief.tileN l)*Branch.rent a i)) (le_of_eq (by unfold reefCost; ring))
      unfold Sour.tact widthK; rw [hx i hi]; let H:= Dial.idrat (More N); have hf:2*s*Fief.tileN l≤ (a+a)/2*↑H.count.val* p.B:=by simpa only [show H.count.val=1 from rfl,Nat.cast_one,mul_one,←two_mul a,mul_div_cancel_left₀ a two_ne_zero] using T.goal -- tune `(2*a)/2`
      have gv := Fief.fen H i p.B l p.B_pos _ s (add_pos T.hint T.hint) T.hood hf (f_then (t i) (mem_filter.mp hi).2)
      have hy:i.image H.parent=i:=by rw [show H.parent=id from funext fun x=>by nth_rw 1 [← Dial.glass x]; exact Ratio.embed_parent .., image_id] -- name
      rw [hy,show (a+a)/2=a from by ring] at gv; exact gv
    unfold reefCost; exact mul_nonneg (by positivity) (mul_nonneg (rent_pos _ _).le (sum_nonneg fun x _=>sum_nonneg fun y _=>(t i).nonn _ _))
 refine ⟨X',he.bigR htJ ?_,?_⟩
 · unfold V0; cases r <;> simpa
 funext x; unfold giveB X' X; simp only [Finset.sum_apply]; rw [sum_comm]; have hMX(i:Openc (More N) d): iQ i.val=∑ S∈ P',F S i:=by
    rw [w]; symm; apply sum_subset (subset_univ P'); intro j _ v; have hpz: W₀ j=0:=Classical.not_not.mp (fun u=> v (mem_filter.mpr ⟨mem_univ _,u⟩)); exact Matrix.ext fun k l=> norm_le_zero_iff.mp (((t j).expo k l|>.bounded _).trans_eq (by rw [hpz]; rfl))
 change J (iQ _)= _; rw [hMX]; -- adjust arguments
 -- sum needs evaluate X S j projections first.
 have hp(S:Sa N): (∑ i:Aura N,(if i=V S then F' S else 0) x)= J (F S (roller T.pos T.roof x)):=by rw [sum_eq_single_of_mem (V S) (mem_univ _),if_pos rfl]; rfl; intro j _ v; rw [if_neg v]; rfl
 simp_rw [hp]
 simp_rw [P0.whirl,Matrix.sum_apply,Finset.sum_smul]; rw [sum_comm (s:=P')]; apply sum_congr rfl; intro i _; rw [sum_comm]

end YM.CF.Swell
