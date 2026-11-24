import YM.CF.Braid.Wish
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Braid
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics Stationary
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators
open Work.F06
variable {α ξ:Type}[Fintype α][DecidableEq α][Fintype ξ] {σ τ A C : ℝ}{M N r t:ℕ}
lemma carps (v:Axis→ℝ)(t:ℕ)(F:CurRun (t+2)→ Space (t+1)→ℂ)(A B C:ℝ)(ha:0 ≤ A)(hb:0 ≤ B)(hc:0 ≤ C)(he:1+2*(t+1)>4 ∨ ∃ i:Axis,q (axes v) i≠0∧ ‖(q (axes v) i)⁻¹‖ ≤ C)(hp:∀ i,Pond M A (F i))(hQ:∀ i,Pond M B (clipP F v i)):
 let n:=t+1; let μ:=liftL n M; let w:=M+μ; let R:=paneR n 1 (w+n)
 let V:= B*(palmJ C n 0 M*mate n μ); let H:= A+V
 FootB F v M (getRank t w R+w) V (getPay t w R H (H*topG 1^n*palmJ C n 1 (w+n))):=by
 intro n μ w R V H; let f:=clipP F v; obtain ⟨U,hU,hV⟩:= triangleL v (t+1) M C hc he B f hb hQ fun p i b=> chr (cardR v (axes p)) (fun j=>F j (axes p)) i b
 have hP: 0 ≤ V:=mul_nonneg hb (mul_nonneg (palm_pos C hc ..) (mate_pos ..)); have hX(j):Pond w H ((F-U) j):= ((hp j).mono le_rfl (Nat.le_add_right ..)).rest ((hU j).mono le_rfl (Nat.le_add_left ..)); let G := F-U
 have hF:Fall G v:=by
    intro p; rw [show (fun j=> G j (axes p))=(fun j=>F j (axes p))-fun j=>U j (axes p) from rfl,sub_p]; ext1 x; simp only [Pi.sub_apply,hV]; exact sub_self _
 exact ⟨U,fun i=>(hU i).mono le_rfl ((show μ ≤ w from Nat.le_add_left ..).trans (Nat.le_add_left ..)),wallS.cheaper _ (thicken v (add_nonneg ha hP) hX hF hc (he.imp_left (by omega))) le_rfl (Nat.le_add_right ..)⟩
-- explicit domination utilities on offsets
-- tame linear and polynomial
variable {w z y:ℕ→ℕ}
abbrev Pad(w:ℕ):ℕ:=1+w
def CapY (w:ℕ→ℕ):Prop:=∃ n:ℕ,∀ M,w M≤ n*Pad M
lemma seedR (t:ℕ):CapY fun M=>t:=⟨t,fun x=>le_mul_of_one_le_right (by omega) (by unfold Pad; omega)⟩
lemma CapY.lives : CapY id:=⟨1,fun i=>by simp [Pad]⟩
lemma CapY.add(hp:CapY w)(hr:CapY y):CapY (fun x=> w x+y x):=by obtain ⟨a,hp⟩:=hp; obtain ⟨b,hr⟩:=hr; exact ⟨a+b,fun x=>by rw [add_mul]; exact add_le_add (hp x) (hr x)⟩
lemma CapY.scal (i:ℕ) (hp:CapY w):CapY (fun x=> i*w x):=by obtain ⟨a,h⟩:=hp; exact ⟨i*a,fun x=>by rw [mul_assoc]; exact Nat.mul_le_mul_left _ (h _)⟩
lemma focked(t:ℕ)(h:CapY w):CapY (fun x=>fock t (w x)):= (h.scal ..).scal _
lemma peaked(t:ℕ)(h:CapY w):CapY (fun x=>peak t (w x)):= focked _ (focked _ h)
lemma stung(t:ℕ)(h:CapY w):CapY (fun x=> scenery2 t (w x)):=peaked _ ((seedR 1).add (peaked _ h))
lemma drone(t:ℕ)(h:CapY w):CapY (fun x=>rowDr t (w x)):= focked _ ((seedR 1).add (focked t h))
lemma paned(t r:ℕ)(h:CapY w):CapY (fun x=> paneR t r (w x)):=by induction t generalizing r w with
 | zero=> exact h
 | succ t ih=> simp_rw [paneR]; exact (peaked _ h).add (drone _ ((stung _ h).add (drone _ (ih _ (stung _ h)))))
lemma swim(t:ℕ)(h:CapY w):CapY (fun x=>rankM t (w x)):=by induction t generalizing w with
 | zero=>exact h
 | succ t ih=>simp_rw [rankM]; exact (h.add (seedR t)).add (ih ((seedR 1).add (h.add (seedR t))))
lemma slimR(t:ℕ)(h:CapY w)(p:CapY y):CapY (fun x=> getRank t (w x) (y x)):=p.add (swim _ (h.add (drone _ p)))
lemma asked_c (h:CapY w):CapY (fun x=>asked (w x)):= (peaked _ h).add (drone _ (stung _ h))
variable {f g:ℕ→ℝ}
def nib (w:ℕ→ℝ):Prop:=∃ C:ℝ,∃ n:ℕ,0≤ C∧∀ i, 0≤ w i∧ w i ≤ C*(Pad i:ℝ)^n
lemma nib_const (v:ℝ)(hp:0 ≤ v):nib fun _=> v:=⟨v,0,hp,fun i=>⟨hp,by simp⟩⟩
lemma nib.mate (h:CapY w):nib fun i=>(w i:ℝ):=by obtain ⟨a,h⟩:=h; exact ⟨a,1,by positivity,fun i=> ⟨by positivity,by rw [pow_one]; dsimp only; exact_mod_cast (h i)⟩⟩
lemma nib.add(h:nib f)(hp:nib g):nib fun i=> f i+g i:=by
 obtain ⟨C,n,ha,h⟩:=h; obtain ⟨D,m,hm,p⟩:=hp
 refine ⟨C+D,n+m,add_nonneg ha hm,fun i=> ⟨add_nonneg (h i).1 (p i).1,?_⟩⟩
 have hb :1 ≤ (Pad i:ℝ):=by unfold Pad; norm_cast; omega
 rw [add_mul]; apply (add_le_add (h i).2 (p i).2).trans; gcongr <;> omega
lemma nib.mul(h:nib f)(hp:nib g):nib fun i=> f i*g i:=by
 obtain ⟨C,n,ha,h⟩:=h; obtain ⟨D,m,hm,p⟩:=hp
 exact ⟨C*D,n+m,mul_nonneg ha hm,fun i=> ⟨mul_nonneg (h i).1 (p i).1,(mul_le_mul (h i).2 (p i).2 (p i).1 ((h i).1.trans (h i).2)).trans_eq (by rw [pow_add]; ring)⟩⟩
lemma nib.pow(h:nib f)(k:ℕ):nib fun i=> f i^k:=by induction k with
 | zero=> simp only [pow_zero]; exact nib_const _ zero_le_one
 | succ i ih=> simp_rw [pow_succ]; exact ih.mul h
lemma bill_m(t:ℕ)(h:CapY w):nib (fun x=>liftCost t (w x)):= (nib_const _ (by norm_num : 0 ≤ (4:ℝ))).mul (nib.mate (focked _ h))
lemma puff_m(h:CapY w):nib (fun x=>puff (w x)):= (nib_const _ (by norm_num : 0≤(4:ℝ))).mul (nib.mate h)
lemma ape(t:ℕ):nib fun _=>topG t:= nib_const _ (by unfold topG; positivity)
lemma met_c(t:ℕ)(h:CapY w):nib (fun x=>meter t (w x)):=(((ape 1).pow t).mul (puff_m (h.add (seedR t)))).mul ((puff_m (h.add (seedR t))).pow t)
lemma rank_c(t:ℕ)(h:CapY w):nib fun x=>rankK t (w x):=by induction t generalizing w with
 | zero=> exact nib_const _ le_rfl
 | succ t ih=> simp_rw [rankK]; exact (met_c t h).add (((nib_const 1 zero_le_one).add ((met_c t h).mul (ape _))).mul (ih ((seedR _).add (h.add (seedR t)))))
lemma panned(C:ℝ)(t r:ℕ)(h:0≤ C)(p:CapY w):nib fun x=>palmJ C t r (w x):=by induction t generalizing w r with
 | zero=> exact nib_const C h
 | succ t ih=>
    simp_rw [palmJ]; let D:=stung t p; apply (bill_m _ p).add; apply nib.mul _ (ape _); apply nib.mul _ (puff_m (D.add (drone t (paned _ _ D)))) -- tune
    exact ((((bill_m t p).mul (ape 0)).mul (bill_m _ ((seedR 1).add (peaked _ p)))).mul ((nib_const 1 zero_le_one).add ((ih _ D).mul (ape _))))
lemma hnd_m(h:CapY w):nib (fun x=> payT2 (w x)):= (bill_m 0 h).add (((((bill_m 0 h).mul (ape _)).mul (bill_m 0 ((seedR 1).add (peaked _ h)))).mul (puff_m (stung 0 h))).mul (ape _))
lemma tat_m(h:CapY w):nib (fun x=>tax0 (w x)):= ((bill_m 0 h).add (((((bill_m 0 h).mul (ape _)).mul (bill_m 0 ((seedR 1).add (peaked _ h)))).mul (puff_m (stung _ h))).mul (ape _))).mul ((puff_m (asked_c h)).pow _)
lemma say_m(t:ℕ)(hw:CapY w)(hp:CapY y)(he:nib f)(h:nib g):nib (fun x=>getPay t (w x) (y x) (f x) (g x)):= (h.mul ((puff_m hp).pow (t+1))).add ((he.add ((h.mul ((puff_m hp).pow _)).mul (ape _))).mul (rank_c _ (hw.add (drone _ hp))))
end YM.CF.Braid
