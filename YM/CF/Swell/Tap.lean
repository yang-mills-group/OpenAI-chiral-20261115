import YM.CF.Swell.Tora
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt Leaf
open Metric Drapes Tulip Lat Branch Cube Tenant Hove Haro Hest Dial Proa Tye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Prism Moto Oath Font Levier Rill
attribute [local instance] loreM loreN boreKSpace boreXN
variable {N B m:Side}{r:ℕ}(k:ℕ) {a b c d t e:ℝ}
variable {P:BudgetPoint}{L:Scree.Loom N}(U:Roof N a e r L)(h:0<e)(hp:P.threshold≤ a)(hT:r+10≤ P.B)(hP:3 ≤ P.B)(hpκ:cipherK r≤ 5*P.B)(hx:HopeT e b t P.order)(hW:P.threshold ≤ t)
variable {V:SOp N}{A Tx:ℝ}{o: Seat N}
variable (σ:Soak o V A Tx e)
open Push.AbsoluteSums Trees Wray Ione Fief
-- Earnings seat pulse.Spark consumes hardware.B.Month.SeatN spaces.
variable {H :ℝ}  -- trim
abbrev distinct_L (M:Bag N)(P:BudgetPoint):Prop:=∀ X Y:Aura N,X.val⊆Y.val→∀ V, V.1∈ Sour.σX P Y ∅ →∀ A:Ids N,M X (V.1,A)= M X V
structure Blip_o (o:Seat N)(M:Bag N)(Γ: Aura N→ℝ)(P:BudgetPoint)(δ:ℕ)(H b L:ℝ) :Prop where
 chant: Bias δ M P H Γ
 pays: ∀ X:Aura N, o ∉ X.val→ M X=0∧Γ X=0
 eats:distinct_L M P
 fee: Cadre.nook (Γ*loom_v L 0 (widthK N P.B) 0) o ≤ b
namespace Blip_o
variable {M' Q':Bag N}{Γ Λ:Aura N→ℝ}{δ:ℕ}{K:ℝ}
lemma lensB(u:Blip_o o M' Γ P δ H b K)(p:Blip_o o Q' Λ P δ H A K):Blip_o o (M'+Q') (Γ+Λ) P δ H (b+A) K:=by
 refine ⟨u.chant.plus p.chant,fun X t=>?_,fun X Y p' V t g=>?_ ,?_⟩
 · simp only [Pi.add_apply, (u.pays X t).1,(u.pays X t).2,(p.pays X t).1,(p.pays X t).2,add_zero,and_self]
 · exact congrArg₂ (·+·) (u.eats X Y p' V t g) (p.eats X Y p' V t g)
 · rw [add_mul]; unfold Cadre.nook; simp_rw [Pi.add_apply,sum_add_distrib]; exact add_le_add u.fee p.fee
end Blip_o
variable {G':Op (Single N)→ FC (Dwell N)} -- tune
variable {Zi:Single N→Single N→FC (Dwell N)}(pG:Glyph G' Zi H)
variable (hH:1 ≤ H)(gA:0<A)(L':ℝ)(uL:0 ≤ L')(pL:2*L'*Fief.tileN 1≤ A/2/2*P.B)
abbrev nold(P:BudgetPoint)(b L H:ℝ):=(P.order+1:ℝ)*H^2*aimV P.B b L
include gA U h σ pG hp hT hP hpκ hx hW hH uL pL
lemma zink_K :∃ M':Bag N, ∃ Γ:Aura N→ℝ, Blip_o o M' Γ P (cipherK r) H (nold P A L' H*Tx) L'∧∀ x:Orbit N,(∑ Y:Aura N,M' Y x)=G' (V (roller h U x).val):=by
 obtain ⟨F,C,p,u,v,z⟩:=σ; let Q(Y:Aura N):= @noteR _ P H C Y; let M:=actsF G' F U h P.B
 have hl:=earned F U h p G' Zi H pG hx hW hp hT hpκ hP; refine ⟨M,Q,⟨hl,fun X p'=>?_,?_ , expF H F p (tally_F (fun S=>(p _).nonn) v) gA uL pL o⟩,fun x=>(lute (P:=P) F U h p G' Zi H pG x).trans (congrArg G' (z (roller h U x)).symm) ⟩
 · let Q'(S:Sa N)(t:S∈ αW P.B X):= u S (fun v=>p' ((mem_filter.mp t).2 ▸ halo_subset _ _ v)); have hx(X:Firing N):X=X:= rfl
   refine ⟨sum_eq_zero fun i u=>?_ , sum_eq_zero fun i u=>?_ ⟩
   · funext V; have hh:F i (roller h U V)=0:=Matrix.ext fun j k=> norm_le_zero_iff.mp (((p i).expo j k|>.bounded _).trans_eq (by rw [Q' i u]; rfl)); unfold Glyph.cure; rw [hh,pG.whirl]; simp
   rw [Glyph.vest,Q' i u]; simp [ledgerV]
 intro X Y k V p' Z; unfold M actsF; rw [Finset.sum_apply,Finset.sum_apply]; apply sum_congr rfl; intro i t; unfold Glyph.cure; apply congrArg G'; apply pact_p h U (p i); intro j u v; let f: Lattice.halo (r+10) i ⊆ Y.val:=Subset.trans (Corona.halo_mono hT (Subset.refl _)) (by rw [←show X.val=Lattice.halo _ i from (mem_filter.mp t).2]; exact k); exact (fern U hp i f V.1 p' j u rfl Z).trans (fern U hp i f V.1 p' j u rfl V.2).symm -- tune
omit pG σ
variable {C':SOp N}(Tq:Ids N)
variable {G:SOp N} (p': Soak o V A Tx e)(w':Solo A c G e)
abbrev ζ_fee (c A:ℝ):= 1+ (2*c+2*c)+2*(Real.exp A+c)+4*c*(Real.exp A+c)
include Tq p' w'
lemma shootM (u: P.supportExponent≤ L'): ∃ (M':Bag N) (Γ:Aura N→ℝ) (E:RegBudget N),
 let D:= (fun x:Chin N=>G x*V x); Blip_o o M' Γ P (cipherK r) H (nold P A L' H *Tx *ζ_fee c A) L'∧ IncX (fun _=>False) E P H (νmeta P A *(2*(c*Tx))) ∧ (∀ X:Scree.Hub N,X.val.1≠ o→ E X=0) ∧ ∀ x:Orbit N,let y:=(roller h U x).val; (∑ Y:Aura N,M' Y x)=Sault.forge (D y) (V y) (V y*(1-G y)) (G y*V y) (G y * V y*(1-G y)) ∧ (P.supportExponent≤L'→ Rue.FleetS P.threshold x.1→flags P.threshold x.1=∅→ exponentL P E x.1= hollow (Matrix.trace (D y))) :=by -- θSet.H 
 -- construct.P budget rent assume pMg externally.Verifier.Hoist only. include p_M to solve Tora.p. 
 have hpZ:Solo A (Real.exp A+c) (fun x:Chin N=>1-G x) e:=Crown.sub (Crown.ident _ _ _) w'
 let D:=fun x:Chin N=> G x*V x; have hvD:=aura_Y p' w' gA.le
 let l':=nold P A L' H
 have H' {G Q0}(r: Glyph (n:=N) G Q0 H){F:SOp N}(pC:ℝ)(p:Soak o F A pC e):=zink_K U h hp hT hP hpκ hx hW p r hH gA L' uL pL
 obtain ⟨M₀,P₀,k0,t0⟩:= H' (pal_v _ hH) _ p'
 obtain ⟨M₁,P₁,k1,t1⟩:= H' (oreV _ hH _) _ hvD
 obtain ⟨M₂,P₂,k2,t2⟩:= H' (tail_k _ hH) _ hvD
 obtain ⟨M₃,P₃,k3,t3⟩:= H' (leg_k _ hH) _ (aura_X p' hpZ gA.le)
 obtain ⟨M₄,P₄,k4,t4⟩:= H' (less_k _ hH) _ (aura_X hvD hpZ gA.le)
 let M:= M₀+M₁+M₂+M₃+M₄; let Q:=P₀+P₁+P₂+P₃+P₄; have he:= (((k0.lensB k1).lensB k2).lensB k3).lensB k4
 obtain ⟨F,W,p,uZ,v,z⟩:=hvD
 have htMW:2*P.supportExponent*(Fief.tileN 1)≤ A/2*P.B:= le_trans (le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left u (by positivity)) (Nat.cast_nonneg _)) pL) (mul_le_mul_of_nonneg_right (by linarith : A/2/2 ≤ A/2) (Nat.cast_nonneg _))
 have hk:= horn_S U h hp hT hP hpκ hx hW o D A _ F W p uZ v z Tq gA htMW H
 refine ⟨M,Q,utter U h o F Tq P,?_ , hk.1,hk.2.1 ,?_⟩
 · convert he using 1; unfold ζ_fee; ring
 intro x y; refine ⟨?_, fun _ p1 p2=>hk.2.2 x p1 p2⟩; unfold M; rw [forkL]; simp only [Pi.add_apply,sum_add_distrib,t0,t1,t2,t3,t4]; abel
end YM.CF.Swell
