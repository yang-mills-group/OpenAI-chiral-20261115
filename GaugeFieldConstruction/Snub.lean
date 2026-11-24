import GaugeFieldConstruction.Snan
/- Incidence Majorant -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock.Wosk
open Pastry Function Set Metric MeasureTheory NormedSpace Filter Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Roots Mew Roots.GJ
variable {I J O V B W G:Type}[LinearOrder I][Fintype I][DecidableEq J][LinearOrder G][Fintype G]
variable (ι:G→J)(a b h r:ℝ)(U:G→ G→Toil I J B)(c d:ℝ)(p:FumedH a b ι U c d)(q:Book0 I J G B)(D:ℝ)(t:Puffion ι q)(s:MajorZ a b h q D)
variable (hr:0≤r)(ha:0≤a)(hb:0≤b)(ht:1≤h)
local notation "WG"=>weightV a b
local notation "WX"=>bil a b
variable (hD:0≤D)(hC:0≤c)
include p hr t
-- iterative genesis.Intake
lemma puff_τ (w:Book0 I J G B)(h:Puffion ι w): Puffion ι (topL U r q w):=by
 refine ⟨fun i w=>?_,fun i w=>?_⟩ <;> obtain ⟨k,v',hT⟩:=List.mem_flatMap.mp w
 · exact (grow_s ι a b r U c d p q t hr k (h.1 k v') (h.2 k v')).1 i hT -- tune b shadow
 exact (grow_s ι a b r U c d p q t hr k (h.1 k v') (h.2 k v')).2 _ hT
omit t
lemma Puffion.app_Q {S R:Book0 I J G B}(p:Puffion ι S)(q:Puffion ι R):Puffion ι (S++R):= ⟨p.1.append q.1,fun i t=>(List.mem_append.mp t).elim (p.2 i) (q.2 i)⟩ -- omit HR
variable (X:I→Book0 I J G B)
lemma puff_K (l:List I)(h:∀ i∈l,Puffion ι (X i)): Puffion ι (Keeps U r X l):=by
 induction l with
 | nil=> exact ⟨fun i t=> by simp [Keeps] at t,fun i t=>by simp [Keeps] at t⟩
 | cons i l ih=> have hx:=ih (fun i t=>h i (List.mem_cons_of_mem _ t)); apply Puffion.app_Q _ _ _ r U c d p hr hx; exact puff_τ ι a b r U c d p (Keeps U r X l) hx hr _ (h i List.mem_cons_self)
-- cost for birth by P.' ℜ
local notation "G0" =>RadBill r c D
local notation "V0"=> Lem I J (Option (G×G)) B
abbrev αR (r u c:ℝ):= max 1 (r*ΘsF r u c)
include t s ht hb ha hC hD
-- $len.Singleton D prime$
lemma birth (e:Lem I J (Option (G×G)) B)(v:0≤e.won)(y:J): let P(i:G):= r* Aqua_D a b r U q i y* G0+r*Aqua_D a b r U q i y*c -- spare charges both legs.
    let R(i:G):=r*G0*privH a b U i y;
    Lee (growL U r q e) (fun x=>costL a b h x y) ≤ αR r G0 c * costL a b h e y + r*wageL a b h e* ((e.val.map Prod.fst).elim 0 P+(e.val.map Prod.snd).elim 0 P+(e.val.map Prod.fst).elim 0 R):=by
 intro P R
 unfold growL; cases hu:e.val with
 | none=> simp only [consA,hu,Option.map_none,Option.elim_none,add_zero,mul_zero]; rw [show Lee ([]:Book0 I J G B) (fun x=>costL a b h x y)=0 from rfl,add_zero]; exact le_mul_of_one_le_left (costsZ a b h _ hb v y) (le_max_left ..)
 | some X0=>
    rcases X0 with ⟨i,j⟩; simp only [mapA,hu,Option.map_some,Option.elim_some]; let T:= toothW U r q i j; have hk:=tooth_pay ι a b h r U c d p q D t s hr ha hb ht hD hC i j; let ht0:= tooth_s ι a b r U c d p q t hr i j
    have he:0≤costL a b h e y:=costsZ _ _ _ e hb v y; have hx:0≤ wageL a b h e:=mul_nonneg (costsE ..) (WP_v _ b _ hb v) -- tune dots
    refine le_trans (lea_p _ _ (fun w=> r*costL a b h e y * WG w+r*wageL a b h e * WX w y) fun w hh=> ?_) ?_
    · have hV:Lite h w.val≤ Lite h e.val:=by rw [hu]; cases w.val with|none=>exact cursorE h ht _|some w=>exact le_rfl
      have hw:= ht0.1 _ hh; have hx0:=WP_union a b r e w ha hb hr v hw w.val y
      apply (mul_le_mul hV hx0 (WP_p a b _ hb (mul_nonneg (mul_nonneg hr v) hw) _) (costsE ..)).trans_eq; unfold wageL costL; ring
    rw [lea_pair, lea_scale, lea_scale]; apply add_le_add ((mul_le_mul_of_nonneg_left hk (mul_nonneg hr he)).trans ?_)
    · apply (mul_le_mul_of_nonneg_left (WP_bill ι a b h r U c d p q D t s hr ha hb ht hD hC i j y) (mul_nonneg hr hx)).trans; apply mul_le_mul_of_nonneg_left _ (mul_nonneg hr hx); have hp:=mul_nonneg (mul_nonneg hr (Aqua_p _ _ _ _ U c d p q t hr hb y i)) hC; unfold P R; linarith
    rw [mul_right_comm]; exact mul_le_mul_of_nonneg_right (le_max_right ..) he
-- final top from straight marks $U` at any inventory, all µ'.
variable (E:Book0 I J G B) -- E universe. 
variable (C:ℝ)
local notation "Gd"=> Tax_D r c d D
abbrev Δ_R (r v c u:ℝ):= u*(r*v+r*c)
abbrev ΔBorn (r v c d C u:ℝ):= αR r v c*C+r*(C*Δ_R r v c u+C*Δ_R r v c u+C*(r*v*d))
omit t s hC hD ht hr ha p
lemma wig_τ (j:G×G→G)(v:∀ i k,j (i,k)=i ∨ j (i,k)=k)(hE:Puffion ι E)(h₀:MajorZ a b h E C)(i:G): Lee E (fun e=> if e.val.map j=some i then wageL a b h e else 0)≤ C:=by
 apply le_trans _ (h₀ (ι i)); refine lea_p _ _ _ fun x t=>?_
 split
 next u=>
    obtain ⟨⟨y,z⟩,w,g⟩:= Option.map_eq_some_iff.mp u; have hx:=hE.2 x t y z w
    have hh:ι i∈x.seat:= by rw [←g]; cases v y z with | inl p=>rw [p]; exact hx.1| inr p=>rw [p]; exact hx.2
    exact (mul_le_mul_of_nonneg_left (le_of_eq (if_pos hh).symm) (costsE ..)) -- tune
 exact costsZ a b h _ hb (hE.1 _ t) _
include t s hC hD ht hr ha p
lemma inn_κ (hE:Puffion ι E)(hx:MajorZ a b h E C)(h0:0≤C): MajorZ a b h (topL U r q E) (ΔBorn r G0 c d C Gd):=by
 intro y; let P(i:G):=r*Aqua_D a b r U q i y*G0+r*Aqua_D a b r U q i y*c; let Tη (i:G):=r*G0*privH a b U i y; let L(f:G→ℝ)(P:G×G→G)(e:V0):= (e.val.map P).elim 0 f
 have htT: 0≤ G0:=by unfold RadBill; positivity
 have hP(i): 0≤P i:= by have hx:0≤Aqua_D a b r U q i y:= Aqua_p _ _ _ _ _ c d p q t hr hb y i; unfold P; positivity
 have hT(i):0≤Tη i:=mul_nonneg (mul_nonneg hr htT) (priv_w _ _ _ _ c _ hb p i y)
 have hs(k:G×G→G)(u:∀ i j,k (i,j)=i ∨ k (i,j)=j)(P:G→ℝ)(v:∀i,0≤P i): Lee E (fun e=>wageL a b h e* L P k e) ≤ C*∑ i,P i:=(mapf_ζ _ _ _ _ _ v (wig_τ ι a b h hb E C _ u hE hx)).trans (mul_sum _ _ _).ge -- tune syntax
 have hu(k:G×G→G)(u:∀i j,k (i,j)=i ∨ k (i,j)=j):Lee E (fun e=> wageL a b h e* L P k e) ≤ C* Δ_R r G0 c Gd:= by
    apply (hs k u _ hP).trans; apply mul_le_mul_of_nonneg_left _ h0; have hg: ∑ i:G,P i=(∑ i:G,Aqua_D a b r U q i y)*(r*G0+r*c):= by rw [sum_mul]; apply sum_congr rfl; intro i _; unfold P; ring
    rw [hg]; unfold Δ_R; exact mul_le_mul_of_nonneg_right (frond_bill _ _ _ _ _ _ _ _ p _ _ t s hr ha hb ht hC hD _ ) (by positivity)
 unfold topL; rw [joinA]; refine le_trans (lea_p _ _ (fun e=> αR r G0 c*costL a b h e y+r*wageL a b h e*(L P Prod.fst e+L P Prod.snd e+L Tη Prod.fst e)) (fun i u=>birth ι a b h r U c d p q D t s hr ha hb ht hD hC i (hE.1 i u) y)) ?_
 unfold ΔBorn; simp_rw [mul_assoc r (wageL ..),lea_pair,lea_scale]; refine add_le_add (mul_le_mul_of_nonneg_left (hx _) (le_trans zero_le_one (le_max_left ..))) (mul_le_mul_of_nonneg_left ?_ hr)
 simp_rw [mul_add (wageL a b h _),lea_pair]; refine add_le_add (add_le_add (hu _ (fun i j=>Or.inl rfl)) (hu _ (fun i j=>Or.inr rfl))) ((hs _ (fun i j=>Or.inl rfl) _ hT).trans (mul_le_mul_of_nonneg_left ?_ h0)); unfold Tη; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (p.pc0 _) (by positivity)
#print axioms inn_κ
end YM.CF.Fock.Wosk
end
