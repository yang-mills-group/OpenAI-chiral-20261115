import YM.SU5.Assay.BSOT
set_option autoImplicit false
open Filter Set
open scoped Topology
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
/-! Two ordinary limits and simultaneous on `t ≥ u s`. To interpret
 actual prices we will take `u s` to cover engravings at `s`.
 `Escrow u` requires both indices go to infinity in that slice. -/
def Escrow (u:ℕ→ℕ):Filter (ℕ×ℕ):=atTop ⊓ principal {i|u i.1 ≤ i.2}
lemma Escrow.visits (u:ℕ→ℕ): Tendsto id (Escrow u) atTop:=tendsto_id'.mpr inf_le_left
lemma Escrow.fst (u:ℕ→ℕ): Tendsto Prod.fst (Escrow u) atTop:=by
 have t:= Escrow.visits u; rw [←prod_atTop_atTop_eq] at t
 exact tendsto_fst.comp t
lemma Escrow.snd (u:ℕ→ℕ): Tendsto Prod.snd (Escrow u) atTop:=by
 have t:= Escrow.visits u; rw [←prod_atTop_atTop_eq] at t
 exact tendsto_snd.comp t
lemma Escrow.pays (u:ℕ→ℕ): ∀ᶠ i in Escrow u,u i.1 ≤ i.2:= le_principal_iff.mp inf_le_right
variable {u v:ℕ→ℕ}
lemma Escrow.travels {I:Type*}{l:Filter I}{s t:I→ℕ}(a:Tendsto s l atTop)(b:Tendsto t l atTop)(c:∀ᶠi in l,u (s i) ≤ t i):
 Tendsto (fun i=>(s i,t i)) l (Escrow u):=by
 have g:=a.prodMk b; rw [prod_atTop_atTop_eq] at g
 exact tendsto_inf.mpr ⟨g,tendsto_principal.mpr c⟩
instance Escrow.fares (u:ℕ→ℕ):NeBot (Escrow u):=
 (Escrow.travels (u:=u) (s:=id) (t:=fun i=>max i (u i)) tendsto_id (tendsto_atTop_mono (fun i=>le_max_left i (u i)) tendsto_id) (Eventually.of_forall fun i=>le_max_right i (u i))).neBot
lemma Escrow.up (h:∀ᶠs in atTop, u s ≤ v s): Escrow v ≤ Escrow u:=by
 have y:∀ᶠi in Escrow v,u i.1 ≤ i.2:=(((Escrow.fst v).eventually h).and (Escrow.pays v)).mono fun _ z=> z.1.trans z.2
 exact le_inf inf_le_left (le_principal_iff.mpr y)

structure BothWays {X:Type*} [TopologicalSpace X] (u:ℕ→ℕ)(a:ℕ→ℕ→X)(b:ℕ→X)(p:X): Prop where
 starts : ∀ᶠs in atTop, Tendsto (a s) atTop (𝓝 (b s))
 next:Tendsto b atTop (𝓝 p)
 together:Tendsto (fun i=>a i.1 i.2) (Escrow u) (𝓝 p)
namespace BothWays
variable {X Y:Type*} [TopologicalSpace X][TopologicalSpace Y]{a a':ℕ→ℕ→X}{b b':ℕ→X}{p q:X}
lemma map (h:BothWays u a b p){f:X→Y}(t:Continuous f): BothWays u (fun i j=> f (a i j)) (f ∘ b) (f p):=
 ⟨h.starts.mono fun _ e=>(t.tendsto _).comp e,(t.tendsto _).comp h.next,(t.tendsto _).comp h.together⟩
lemma raise (h:BothWays u a b p)(t:∀ᶠs in atTop,u s ≤ v s):BothWays v a b p:= ⟨h.starts,h.next,h.together.mono_left (Escrow.up t)⟩
lemma congr' (h:BothWays u a b p)(t:∀ᶠs in atTop,b s=b' s∧∀j≥u s,a s j=a' s j):BothWays u a' b' p:=by
 refine ⟨?_,h.next.congr' (t.mono fun _ z=>z.1),h.together.congr' ?_⟩
 · exact (h.starts.and t).mono fun s z=> ((z.2.1 ▸ z.1):Tendsto (a s) atTop (𝓝 (b' s))).congr' ((eventually_ge_atTop _).mono z.2.2)
 exact (((Escrow.fst u).eventually t).and (Escrow.pays u)).mono fun _ z=>z.1.2 _ z.2
lemma via [T2Space X](h:BothWays u a b p)(k:BothWays v a b' q): p=q:=by
 let r(s:ℕ):=max (u s) (v s)
 exact tendsto_nhds_unique (h.raise (v:=r) (Eventually.of_forall fun _=>le_max_left ..)).together
    (k.raise (v:=r) (Eventually.of_forall fun _=>le_max_right ..)).together
lemma pack {c:ℕ→ℕ→Y}{d:ℕ→Y}{r:Y}(h:BothWays u a b p)(k:BothWays u c d r):BothWays u (fun s t=>(a s t,c s t)) (fun s=>(b s,d s)) (p,r):=
 ⟨(h.starts.and k.starts).mono fun _ z=>z.1.prodMk_nhds z.2,h.next.prodMk_nhds k.next,h.together.prodMk_nhds k.together⟩
lemma const (u:ℕ→ℕ)(p:X):BothWays u (fun _ _=>p) (fun _=>p) p:=⟨Eventually.of_forall fun _=>tendsto_const_nhds, tendsto_const_nhds,tendsto_const_nhds⟩
end BothWays
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
