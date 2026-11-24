import YM.CF.Floe.Arc
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floe
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Filter NormedSpace Function Lattice Lat SU Fock Phase Cube Tenant Branch Drapes Metric Finset
attribute [local instance] opCStarAlgebra
variable {N m B:Side}{a b c d r e:ℝ}
local notation "M" => Model N
local notation "D"=>Kelp N a
open LedgerP
def vane(a K:ℝ):ℝ:=(∑' i:ℕ, Real.exp (-a/2*i)*(quota*((i:ℝ)+1)^4))*K
lemma seeP {F:pMat}{K:ℝ}{u:Bool}(h:certS F u u b a K)(p:0<b) (i:Δ):∃ V Y, Spends (ku (a:=a) (N:=i.1)) V Y (b/2) (vane b K)∧(∀ S, Looks _ (V S))∧∀ x:Kelp i.1 a, (F i x.val).trace=∑ S,V S x:=by
 obtain ⟨H,A,L,g,x⟩:=h i; refine ⟨fun S z=> (H S z).trace, fun S=>ledgerV (A S), ⟨fun S=>ledgerT (L S).toTicket,fun z=>tall (fun i=> (L i).toTicket) g p (ku_cap ..) ζq z⟩,?_,fun z=>?_⟩
 · intro S T t γ l; exact DifferentiableOn.fun_sum (u:=Finset.univ) fun j _=> ((L S).fuel j j _ t γ l) -- binder tune
 change (F i z.val).trace=_; have he:(F i z.val)=∑ S,H S z:=x z; rw [he,Matrix.trace_sum]
private lemma vow_ct : Continuous vow := continuous_pi fun i => by unfold vow; split <;> fun_prop
private lemma θCt : Continuous (skin (N:=N)):=by
 unfold skin; refine Continuous.prodMk (continuous_pi fun i=> ?_) (continuous_pi (fun i=>continuous_pi fun j=>?_))
 · let F(g:E):=color matter g; have hv:Continuous F:=by
    refine continuous_matrix fun i j=>?_ ; exact continuous_const.mul (matter_cont.matrix_elem i.2 j.2) -- note
   exact vow_ct.comp (hv.comp ((continuous_apply i).comp continuous_fst))
 exact vow_ct.comp (localPair_cont.comp ((continuous_apply _).comp ((continuous_apply _).comp continuous_snd)))
def Shove(p:0<a)(V:Seal (Site (More N))→ ↑(Kelp N a)→ℂ): Seal (Site (More N))→Own N→ℂ:=fun z x=>V z (uθ x p)
lemma shoves {f:Seal (Site (More N))→ ↑D→ℂ}{Y:Seal (Site (More N))→ℝ}{p:0<a}(h:Spends (ku (a:=a) (N:=N)) f Y b c): Spends (slotK N) (Shove p f) Y b c:=by
 refine ⟨fun S=>?_,h.payline⟩; obtain ⟨z,y,d,k,l,u⟩:= h.stamped S; refine ⟨z,y,fun g x=> ?_,k.comp ((θCt.comp continuous_subtype_val).subtype_mk _),fun x=>l _,fun x y=>?_⟩ -- f drives morph
 · unfold Shove; rw [show uθ ((slotK N).drive g x) p=ku.drive g (uθ x p) from Subtype.ext (scene ..).symm]; exact d ..
 exact le_trans (u _ _) (by rw [Floe.moment]) -- maybe binding
open Phase
structure GripK {k: Part m B}(W: Scroll m B k) (a b c:ℝ) :Prop where
 meter:ScaleK b c W
 ext(k:0<a) :∃ (F G:Stamp m B → (Kelp (CSide m B) a) →ℂ), W.hull=Shove k F ∧ W.phi=Shove k G∧ (∀ i, Looks _ (F i)∧ Looks _ (G i)) ∧Spends (ku (a:=a) (N:=CSide m B)) F W.dull b c∧ Spends (ku (a:=a) (N:=CSide m B)) G W.din b c
lemma caps :∃ a b c:ℝ,0<a ∧ 0<b∧0<c ∧∀ m B:Side,∀ k:Part m B,∃ W: Scroll m B k, GripK W a b c:=by
 obtain ⟨a,b,r,p,q,h,U,V⟩:= LedgerP.like ψOp ψZp; let H:=max 1 (vane a r); have hp:vane a r ≤H:=le_max_right ..
 refine ⟨b,a/2,H,q,half_pos p,lt_max_of_lt_left zero_lt_one,fun m B k=>?_⟩; let X:= CSide m B; let Z:= codify k -- implicit m B ambiguous
 obtain ⟨F,Y,x,g,f⟩:= seeP U p Z; obtain ⟨G,L,u,Q,H'⟩:= seeP V p Z
 refine ⟨⟨Shove q G,Shove q F,L,Y⟩, ⟨?_,?_⟩⟩
 · refine ⟨SpendP (shoves u) le_rfl hp,SpendP (shoves x) le_rfl hp,?_ ,?_⟩
   · intro x; have hx:= H' (uθ x q); change Matrix.trace (pencil (zκ Z (skin x.val)))=_ at hx; rw [zκ_l] at hx; exact hx
   intro x; have he:=f (uθ x q); change Matrix.trace (pencil (omenP Z (skin x.val)))=_ at he; rw [omen_l] at he; exact he
 exact fun k=> ⟨G,F,rfl,rfl,fun i=>⟨Q i,g i⟩,SpendP u le_rfl hp,SpendP x le_rfl hp⟩
end YM.CF.Floe
