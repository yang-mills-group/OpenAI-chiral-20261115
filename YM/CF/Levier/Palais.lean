import YM.CF.Levier.Pyle
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Proa Urn
open Kennel
variable {L N P:Side}{j:ℕ}{A:Type*}(K:WG A)(S:A→Male)(G:Ratio N P)(h:Odd G.count.val)(i:A)
variable {b r:Bool}(a:Shape)(B:ColorT b)(U:UNI SpinIdx)
section story
variable (x y:Nom N P)(w:∀ u (z:Nom N P),z=x∨z=y→Along j G.count h (Thread j) u (S i) G (unionP z))
variable (X:Bool→ Op (Iota G)) -- unused
local notation "R"=>pflux a G U B
local notation "g₀"=>foal j _ (S i) G
variable (C: Op (Iota G))(t: TagG (foal j true (S i) G (unionP x)) C)
include w t
lemma piano (hp:∀ u:Bool, sings b R (foal j u (S i) G (unionP x))=foal j (u.xor r) (S i) G (unionP y) ∧ sings b R (wh j G.count h u (S i) G (unionP x))= wh j G.count h (u.xor r) (S i) G (unionP y) ∧ sings b R (ticketT (Thread j) u (S i) G (unionP x))=ticketT (Thread j) (u.xor r) (S i) G (unionP y))(g:IsUnit (1+ bentT (pine j G.count h (Thread j) true (S i) G (unionP x)) (wh j G.count h true (S i) G (unionP x)) (ticketT (Thread j) true (S i) G (unionP x)) C))(p:IsUnit (1+bentT (pine j G.count h (Thread j) false (S i) G (unionP x)) (wh j G.count h false (S i) G (unionP x)) (ticketT (Thread j) false (S i) G (unionP x)) (-star C))) :
 let M:=S i; let X(z:Nom N P)(v):= pine j G.count h (Thread j) v M G (unionP z); let Y(z:Nom N P)(v):=wh j G.count h v M G (unionP z); let W(z:Nom N P)(v):=ticketT (Thread j) v M G (unionP z); traitP (Y y true) (X y true) (W y true) (Thera.jazz r (sings b R C))= Thera.jazz r (sings b R (traitP (Y x true) (X x true) (W x true) C)):=by
 intro M X Y W; let F(u:Bool)(x:Nom N P):=foal j u M G (unionP x); let f:=sings b R; have he(u z)(p:z=x∨z=y):Clad (F u z) (Y z u) (W z u) (W z (!u)) (X z u):= court _ _ _ _ _ _ _ (w u z p)
 have hm(u):f (X x u)= X y (u.xor r):= frame_turn R _ _ _ _ _ _ _ _ _ _ (he _ _ (Or.inl rfl)) (he _ _ (Or.inr rfl)) b (hp u).1 (hp u).2.1 (hp u).2.2
 let T(z v D):=traitP (Y z v) (X z v) (W z v) D; have ht(u:Bool)(D:Op (Iota G))(g:IsUnit (1+bentT (X x u) (Y x u) (W x u) D)): T y (u.xor r) (f D)= f (T x u D):=by unfold T; rw [←hm,← show f (Y x u)=Y y (u.xor r) from (hp u).2.1,← show f (W x u)=W y (u.xor r) from (hp u).2.2]; exact spice R _ _ _ _ g
 have hv: Y x false= 1-Y x true:= wh_neg _ _ _ G true _ _; have hx: F false x=1-F true x:= foil_neg _ G true _ _; have hl:T x false (-star C)= -star (T x true C):=by
    unfold T; rw [hv]; apply reflectL (he _ x (Or.inl rfl)) (by rw [←hv,←hx]; exact he false x (Or.inl rfl)) _ g; rw [← hv]; exact p; exact t
 cases r; exact ht true C g
 rw [show Thera.jazz true (sings b R C)= f (-star C) by simp only [f,Thera.jazz,ite_true,singT,win_n,win_s,map_neg,map_star]]
 change T y (false.xor true) _= _; rw [ht false _ p, hl]; unfold f Thera.jazz; simp only [singT,win_n,win_s,map_neg,map_star,ite_true]; rfl
end story
end YM.CF.Levier
