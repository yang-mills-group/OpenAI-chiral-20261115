import GaugeFieldConstruction.QuarryRT
/-!
 # partial shore local shell pricing, costs & capabilities all vector variations and Mink early/late swap.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe Surface
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
variable {n:ℕ}(k:Fin n)
local notation "ιᵢ" => k.castSucc
local notation "ιⱼ" => k.succ
local notation "Nx" => τNearRT k
lemma heightTieRT (y:Heights (n+1))(v:(Nx).Fleck y): (Nx).switch (dawn y)=dawn y:=by
 ext1 i; rw [NearPair.switch_at]; by_cases p:i=ιᵢ
 · simp [p,switchNextRt,dawn,place,← (show y ιᵢ=y ιⱼ from v.willing.1)]
 by_cases q:i=ιⱼ
 · simp [q,switchNextRt',dawn,place,(show y ιᵢ=y ιⱼ from v.willing.1)]
 rw[NearPair.s,Equiv.swap_apply_of_ne_of_ne p q]
lemma pointIRt (y:Heights (n+1))(v:(Nx).Fleck y) : (𝓝[fields (n+1)] (dawn y)).NeBot:= by
 have h: MapsTo shade (tube (n+1)) (fields _):=fun p h=>h
 apply mem_closure_iff_nhdsWithin_neBot.mp; rw [← im_glow (0:Points (n+1)) (dawn y)]; exact h.closure (cont_sh _) (v.first _)
variable {G:Gauge}{L:Register G}{S:Table L}{Y:Surface S}{B:∀ i, Blanket i}{F:Waves S}{X:Y.Aurora B}
variable (T:Axis→Axis→ S.Union)(e:MintDΛ (X:=X) T) (p:X.FullBody F)(j:(B (n+1)).Modified)
variable (V:Fin n→ S.Union)(a:Axis)
abbrev TxRT (i:Axis):= addXRT k V (T i a)
variable (y:Heights (n+1))(v:(τNearRT k).Fleck y)
abbrev νRT (i:Axis) := partialXRT (B:=B) (Y:=Y) (TxRT k T V a i) (dawn y)
abbrev μRT (i:Axis) := (Nx).flipW (partialXRT (B:=B) (Y:=Y) (TxRT k T V a i ∘ (Nx).s) ((Nx).switch (dawn y)))
noncomputable abbrev CtimeRt (i:Axis): Distn (Points (n+1)):= νRT (B:=B) (Y:=Y) k T V a y i-μRT (B:=B) (Y:=Y) k T V a y i
local notation "Δrt" => CtimeRt (B:=B) (Y:=Y) k T V a y
lemma reverseTxRt (i:Axis) : TxRT k T V a i= Function.update (addXRT k V 0) ιᵢ (T i a):=by
 ext1 b; cases b using Fin.succAboveCases k.castSucc <;> simp[TxRT,addXRT,k.castSucc.succAbove_ne]
lemma flipTxRt (i:Axis) : TxRT k T V a i ∘ (Nx).s= Function.update (addXRT k V 0 ∘ (Nx).s) ιⱼ (T i a):=by
 rw [reverseTxRt]; ext1 b; by_cases u:b=ιⱼ; · simp [u,switchNextRt']
 have h: (Nx).s b ≠ ιᵢ:= fun w=> u ((Nx).s.injective (w.trans (switchNextRt' k).symm)); simp only [Function.comp_apply,Function.update_of_ne h,Function.update_of_ne u]
include p j v e
lemma ΔrtΛL (g: Joint (n+1))(h:HasCompactSupport ⇑g): (∑ i:Axis,(CtimeRt (Y:=Y) (B:=B) k T V a y i) (DriftΛL (NSF.Points.direction ιᵢ i) g))=0:=by
 simp only [CtimeRt, μRT,νRT, sub_apply, NearPair.flipW,ContinuousLinearMap.comp_apply,ΔSwitchRT]; rw[sum_sub_distrib]; apply sub_eq_zero.mpr
 have ht: HasCompactSupport ⇑(along (Nx).switch.toContinuousLinearEquiv g):= h.comp_homeomorph (Nx).switch.toHomeomorph
 conv_lhs=> arg 2; ext i; rw [reverseTxRt]
 conv_rhs=> arg 2; ext i; rw [flipTxRt,heightTieRT k y v]
 rw [reinsLaRt T e p j a v.here (pointIRt k y v) _ ιᵢ g h,reinsLaRt T e p j a v.here (pointIRt k y v) _ ιⱼ _ ht]
abbrev LambdaStampRT (f:Joint n)(b:Test4)(i:Axis) := CtimeRt (Y:=Y) (B:=B) k T V a y i (χTestRT k b f)
variable (w:∀ i:Axis,IsVanishingOn (fun f=>CtimeRt (B:=B) (Y:=Y) k T V a y i f) (τNearRT k).gap)
include w
lemma pricesSteadyRt (h g:Axis→Test4)(b c: Test4)(e':HatchRT b h)(s:HatchRT c g)(f:Joint n)(q:HasCompactSupport ⇑f): (∑ i:Axis, LambdaStampRT (B:=B) (Y:=Y) k T V a y f (h i) i)= ∑ i:Axis, LambdaStampRT (B:=B) (Y:=Y) k T V a y f (g i) i:=by
 obtain ⟨U,hu,u⟩:= hatchBreakRt b c h g e' s
 unfold LambdaStampRT; have H(i:Axis): Δrt i (χTestRT k (h i) f) - Δrt i (χTestRT k (g i) f)= Δrt i (DriftΛL (NSF.Points.direction ιᵢ i) (χTestRT k U f)):= by
    rw [priceDiffRt,← map_sub,← sub_eq_zero,← map_sub,show χTestRT k _ f - χTestRT k _ f - χTestRT k _ f=χTestRT k (h i-g i-(DmoveRT i U)) f from ?_]
    · exact w i _ (priceWithinRT _ _ (u i) f)
    ext1 x; obtain ⟨w,rfl⟩:=(κMoverRT k).surjective x; simp only [sub_apply,priceIRT,sub_mul]
 rw [← sub_eq_zero,← sum_sub_distrib]; simp_rw[H]; exact ΔrtΛL k T e p j V a y v _ (priceCompRt k U hu f q)
#print axioms pricesSteadyRt
end YM.NSF.Boundary
end
