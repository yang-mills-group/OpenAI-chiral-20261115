import YM.CF.Brace.Ways
/-! Continuous rephasing. Canonical on any generated/capped point. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Brace
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase MeasureTheory
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m B: Side}
abbrev Duet(m B:Side):= Skin m B → Sheen m B→Sheen m B→ℂ
def herald (m B:Side)(F:Duet m B)(U:Skin m B)(X:Sheen m B)(v:Cue m):ℂ:= (law m B U v:ℂ)* F U (starfish m B U v) X
def song(m B:Side)(F:Duet m B)(U:Skin m B)(X:Sheen m B):= ∫ v, herald m B F U X v ∂rains m
variable {F:Duet m B}{j:ℕ}{e p:ℝ}{M:Tulip.Male}(g:enoughV B e p)(he:0≤e)(h:Cane (CSide m B) j M e p F)
include g he h
def Chord(m B:Side)(e p:ℝ):= {x:Skin m B×Sheen m B| Guard x.1 e∧ Slow x.1 (hook x.2) p}
omit g he h in
lemma art_c : LocallyCompactSpace (Chord m B e p):=by -- open Slow
  let U:= {x:Skin m B×Sheen m B|Guard x.1 e}; let V: Set (Skin m B×Sheen m B):={x|Slow x.1 (hook x.2) p}
  have hp:IsOpen V:=by
    unfold V Slow; simp_rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite; intro i; apply isOpen_iInter_of_finite; intro t
    apply isOpen_lt _ continuous_const; apply Continuous.norm
    have hz(i:Site (Domain m B)): Continuous (fun x:Skin m B×Sheen m B=>hook x.2 i):=by unfold hook; fun_prop
    let F : Skin m B × Sheen m B → E:=fun x=>x.1 (i,t)
    have hf:Continuous F:= (show Continuous (fun x:Skin m B=>x (i,t)) from continuous_apply _).comp continuous_fst
    have hh:=hf.prodMk (hz (i+step t)); have he:= turn_cont.comp hh; exact he.sub (hz i)
  have he:IsClosed U:= (cover_closed _ _).preimage (f:=fun x:Skin m B×Sheen m B=>x.1) continuous_fst
  exact (he.isLocallyClosed.inter hp.isLocallyClosed).locallyCompactSpace
lemma music_c:Continuous (fun t:Chord m B e p ×Cue m=>herald m B F t.1.val.1 t.1.val.2 t.2):=by
 let U:= Skin m B × Cue m; let L:U→ℝ:=fun t=>law m B t.1 t.2; let X:=Chord m B e p
 let l:=(↑X) × Cue m; let T:=fun x:l=> (x.1.val.1,x.2); let A: Set U:={x|ZeroF m B x.1 x.2}; let f:l→ Gaz (CSide m B):= fun x=> (x.1.val.1,starfish m B x.1.val.1 x.2,x.1.val.2);
 have ht: Continuous T:=(continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd
 rw [←continuousOn_univ]; apply wear (fun x:l=> F (f x).1 (f x).2.1 (f x).2.2) L Set.univ A T (law_cont ..) ht _ (law_stock m B) (open0 m B)
 refine h.cap.comp (f:=f) ?_ ?_
 · have hs : Set.MapsTo T (Set.univ ∩ T ⁻¹' A) {t| Guard t.1 e∧ZeroF m B t.1 t.2}:=fun i h=>⟨i.1.property.1,h.2⟩
   let H : l → Sheen m B:=fun x=>x.1.val.2; have hp:Continuous H:= continuous_snd.comp (continuous_subtype_val.comp continuous_fst)
   exact ((continuous_fst.comp ht).continuousOn).prodMk (((starfish_c (m:=m) g he).comp ht.continuousOn hs).prodMk hp.continuousOn)
 intro t hg; exact ⟨t.1.property.1,starK g he t.1.property.1 hg.2,t.1.property.2⟩
lemma song_c:ContinuousOn (fun x:Skin m B×Sheen m B=>song m B F x.1 x.2) (Chord m B e p):=by
 letI : LocallyCompactSpace (Chord m B e p) := art_c
 rw [continuousOn_iff_continuous_restrict]; exact net_cont _ _ (music_c g he h)
lemma scoreL (U:Skin m B)(X:Sheen m B)(hc:Guard U e)(x:Slow U (hook X) p): Integrable (herald m B F U X) (rains m):=by -- p shadow
 let t:Chord m B e p:=⟨(U,X),⟨hc,x⟩⟩; let Z: Cue m→ ↑(Chord m B e p)×Cue m:=fun i=>(t,i)
 apply net_compact; exact (music_c g he h).comp (f:=Z) (continuous_const.prodMk continuous_id)
lemma song_no (U:Skin m B)(p':Guard U e)(x y:Sheen m B)(hx:Slow U (hook x) p)(hy:Slow U (hook y) p): song m B F U y=song m B F U x+F U x y:=by
  let A:= F U x y; let f := law m B U; have ht (v : Cue m):herald m B F U y v= herald m B F U x v+(f v:ℂ)*A:=by
    by_cases H:f v=0; unfold f at H; simp [herald,H,f]
    have hz:=h.spore U p' _ (starK g he p' (law_rich m B U v H)) x hx y hy; unfold herald; rw [←hz,mul_add]
  have hw: Integrable (fun v=>(f v:ℂ)*A) (rains m):=net_compact (((Complex.continuous_ofReal.comp ((law_cont m B).comp (show Continuous (fun x:Cue m=>(U,x)) from continuous_const.prodMk continuous_id)))).mul continuous_const)
  unfold song; rw [show herald m B F U y = herald m B F U x + (fun v=>(f v:ℂ)*A) from funext ht]; simp only [Pi.add_apply]; rw [integral_add (scoreL g he h _ _ p' hx) hw, integral_mul_const,integral_complex_ofReal,rain_law,Complex.ofReal_one,one_mul]
lemma song_g (U:Skin m B)(p':Guard U e)(x:Sheen m B)(hx:Slow U (hook x) p)(t:Site (Domain m B)→E): song m B F (gauge t U) (feast t x)=song m B F U x:=by
 unfold song; rw [← rain_subst m B t]; apply integral_congr_ae; apply Eventually.of_forall; intro v; unfold herald; dsimp only; rw [law_g]; by_cases hz:law m B U v=0; simp [hz]
 have ht:= law_rich m B U v hz; rw [starG g he p' ht t,h.gour U p' _ (starK g he p' ht) x hx t]
end YM.CF.Brace
