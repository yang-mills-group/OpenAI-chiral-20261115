import YM.CF.Yaw.Pith
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Yaw
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
open Scion PetalP
variable {A n M:Type}[SemilatticeSup A][OrderBot A][Fintype A][DecidableEq A][LinearOrder n][Fintype n][LinearOrder M][Fintype M]
local notation "N'"=> LeanV n
local notation "K"=> LeanV M
abbrev oasis(n:Type):=Twig n
structure OfferS(B:Raid K)(Q:Twig n→ Track A ℝ)(c:Twig n→Track A (Raid K))(w:Twig n→Twig n→Track A (Raid K)):Prop where
 peg: Turner B
 knee:∀ i,ownH ℝ A ≤ Q i
 sail:∀ i,0≤ c i
 score:∀ i j,0≤ w i j
 toll:∀ i,rateT B (c i)+∑ j:Twig n,rateT B (w i j) ≤ Q i
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{z:E}{k:ℕ}
structure PoseS (K':E→ A→ Weave n M)(F:Twig n→Track A (E→FC K))(W:Twig n→ Twig n→ Track A (E→FC K))(z:E)(a:A):Prop where
 legs i: i≤a → ∀ v: Twig n,∀ᶠ y in 𝓝 z,lank (K' y i).seats v=view i (F v) y
 eyes i:i ≤ a→∀ v t:Twig n,∀ᶠ y in 𝓝 z,Stilo.price (K' y i).pals (LeanV M) v t=view i (W v t) y
abbrev deeds (F:Track A (E→FC K))(k:ℕ)(x:E)(a:A)(C:Track A (Raid K)):=∀ i:A,i≤a→ Woody k (F i) x (C i)
structure TramS (K':E→ A→ Weave n M)(z:E)(k:ℕ)(a:A)(c:Twig n→Track A (Raid K))(w:Twig n→Twig n→Track A (Raid K)):Prop where
 scene:∃ F:Twig n→Track A (E→FC K),∃ W:Twig n→Twig n→Track A (E→FC K),PoseS K' F W z a ∧ (∀ i,deeds (F i) k z a (c i)) ∧ (∀ i j,deeds (W i j) k z a (w i j))
local notation "K₀"=> Twig n
local notation "vext"=> (twigExt : LeanV n ↪ Twig n)
local notation "veau"=> (twigCab : Oboe n ↪ Twig n)
variable {B:Raid (LeanV M)}{Q:Twig n→ Track A ℝ}{c:Twig n→ Track A (Raid (LeanV M))}{w:Twig n→Twig n→ Track A (Raid (LeanV M))}{U:PetalP (LeanV n)}{L:PetalP (Oboe n)}
lemma scale_p {F:E→FC K}{y:E→ℂ}{u:Raid K}{r:ℝ}(p:Pence k y z r)(h: Woody k F z u): Woody k (fun x=>y x • F x) z (r • u):=by
 refine ⟨h.own.mono fun i h=> spanS h _, fun i=> Woody.haveP h i |> fun v=> ?_⟩; exact (p.twice v).germ (Eventually.of_forall fun i=> (Pastry.crumb_scale ..).symm)
lemma rateQ(s:ℝ)(c:Track A (Raid K)):rateT B (s • c)=s • rateT B c:=by funext i; simp [rateT,joinV,Finset.mul_sum,mul_left_comm]
lemma rateF {I:Type}[Fintype I](X:I→ Track A (Raid K)):rateT B (∑ i,X i)=∑ i, rateT B (X i):=funext fun i=>by simp [rateT,joinV,Finset.mul_sum]; rw [sum_comm] -- tune needs B included
lemma landQ {ι ℐ:Type}(p:ι→ℐ)(Q:ℐ→Track A ℝ)(L:List ι):payH Q (L.map p)=payH (Q∘p) L:=by induction L with| nil=> rfl| cons i l ih=> exact congrArg (crank _) ih
variable (U L)
lemma pledgeL (p:OfferS B Q c w) (h:0≤U.led)(g:0≤L.led) : ∃ W:Track A (Raid K),0≤W ∧ rateT B W ≤ crank (share U (Q∘vext)) (share L (Q∘veau)) ∧∀(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](a:A)(z:E)(k:ℕ)(T:E→ A→Weave n M)(X:E→FC (LeanV n))(Y:E→FC n), TramS T z k a c w → Meant z k U put X → Meant z k L bell Y →∃ F:Track A (E→FC K), (∀ s,s ≤ a→∀ᶠ y in 𝓝 z,issue (T y s) (X y) (Y y)= view s F y)∧deeds F k z a W:=by
 choose A' j t u using fun (i:U.slots)(r:L.slots)=>lunar B (vext) (veau) (twigExt).injective (twigCab).injective (fun i j (p:Sum.inl i=Sum.inr j)=>by contradiction) Q p.peg p.knee c w p.sail p.score p.toll (U.roll i) (L.roll r)
 let C (i r):=(U.led i*L.led r) • A' i r; have he(i:U.slots)(r:L.slots):0≤ U.led i*L.led r:=mul_nonneg (h i) (g r)
 refine ⟨∑ i,∑ j, C i j, sum_nonneg (fun i _=>sum_nonneg fun k _=> smul_nonneg (he i k) (j i k)), ?_, fun E _ _ a z k T X Y fY y w'=>?_⟩
 · rw [share,share,ray_s,rateF]; apply sum_le_sum; intro i _; rw [crank_C,ray_s,rateF]; apply sum_le_sum; intro r _; unfold C; rw [rateQ]; refine (smul_le_smul_of_nonneg_left (t i r) (he i r)).trans ?_; unfold Hake.crew; rw [tiny_p,landQ,landQ,ray_p,crank_C (U.led i • payH (Q ∘ vext) (U.roll i)) (payH _ _),ray_p,smul_smul,mul_comm] -- tune
 obtain ⟨F,W,b,b',G⟩:=fY.scene; obtain ⟨x,h,h'⟩:=y.post; obtain ⟨r,j',k'⟩:=w'.post
 let S(i:U.slots)(a:L.slots):=cue (U.roll i) (L.roll a); let X'(i u t v):=(x i v*r u v) • spanned F W (S i u) t v
 have he(s:A)(p:s ≤ a):∀ᶠ y in 𝓝 z,(∀ v:Twig n,lank (T y s).seats v=view s (F v) y) ∧ (∀ i j:Twig n,Stilo.price (T y s).pals (LeanV M) i j=view s (W i j) y):= Eventually.and (eventually_all.mpr (b.legs s p)) (eventually_all.mpr fun i=>eventually_all.mpr (b.eyes s p i))
 refine ⟨∑ i, ∑ j, X' i j,fun i k=>?_, fun s l=>?_⟩
 · filter_upwards [h',k',he i k] with y p p' H; have ht(a:U.slots)(b:L.slots):issue (T y i) (x a y • rollC put (U.roll a)) (r b y • rollC bell (L.roll b))=view i (X' a b) y := by
      rw [map_smul,map_smul, LinearMap.smul_apply,smul_smul,mul_comm, ring_u]; simp_rw [show lank (T y i).seats=(fun j=>view i (F j) y) from funext H.1, show Stilo.price (T y i).pals K=(fun j k=>view i (W j k) y) from funext fun j=>funext (H.2 j), ←stave E A] -- tune
      simp [view,Finset.sum_apply,X',Finset.smul_sum,S]
   rw [p,p',map_sum]; simp only [PetalP.Cane,LinearMap.sum_apply,map_sum]; simp_rw [ht]; simp only [Stilo.view, Finset.sum_apply]; rw [sum_comm, sum_comm (s:= deckX i)]; apply sum_congr rfl; intro j _; rw [sum_comm]
 simp only [Finset.sum_apply]; refine Woody.sumV fun i _=>Woody.sumV fun t _=> ?_; refine scale_p ((h i).twice (j' t)) (u i t E z k s W F (fun i v=>?_ ) (fun i' _ S k=>b' i' _ (k.trans l)) (fun i _ j _ S k=>G i j _ (k.trans l))); filter_upwards [he i (v.trans l)] with y h; exact ⟨(T y i).pals,(T y i).seats,(T y i).ward.1,(T y i).ward.2,fun _=>(h.1 _).symm,fun j k=> (h.2 j k).symm⟩
end YM.CF.Yaw
