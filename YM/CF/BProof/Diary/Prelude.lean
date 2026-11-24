import YM.CF.BProof.Diary.Station
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Diary
open Function Filter NormedSpace Finset
open Lattice Tenant Lat Cube Skye RG Wilson Push.SectorMeasure Precision
open Vale Vale.Grace Hom Py Paige Rush Scroll Scree Jet Vault Drapes
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Pressure
variable {N B : Side} {K : Teller SU.group} {P : Patch} {R : ChartRatio SU.group}
variable (V : Grace K P R) {d : ℝ} {F : Grasp V.U B d} {W : GivenX V F} {x : ℝ} (J : Robes N V W)
variable (M:Side) {N₀ : ℕ} (X : Month x 1 6 2 N₀ V W) (h : ℝ) (q : Chi) (R₀ δ : ℝ → ℝ)
open Start
include V
lemma orderK :1 ≤ K.j:=by have hh:=V.L.lobby; have ht:=P.order_cut; omega -- include V
-- fix Press, k and `W0_B` prechoices further before Lore cutoff. 
lemma curtain : Nonempty (TimeSupport V) := by
 obtain ⟨C,Kc⟩:= LocalH.actual SU.group; obtain ⟨ℒ,f⟩:= Release.stock C Kc; obtain ⟨K,H⟩:= chart_bought SU.group 1 one_pos; obtain ⟨p⟩:= Face.available; obtain ⟨h,u⟩:= Gates.fix K ℒ p _ _ _ _ ‹Teller SU.group›.top.width_pos ‹Teller SU.group›.top.paths_pos.le (zero_le_one.trans V.W.rental); exact ⟨h⟩ -- shadow K & inference
variable(u:ℝ) -- q purchased in elm_B option. suitable before $δ$. tempo independent of lease H.Spin
structure Prelude where
 S: TimeSupport V
 D: Tempo V
 E: Rhythm.Essence D u
namespace Prelude
lemma liftE(p:0<u): Nonempty (Prelude V u):=by
 obtain ⟨D⟩:=Spin.ready V.width1 V.width2 V.pos1 V.pos2 _ (orderK V); obtain ⟨S⟩:= curtain V; obtain ⟨E⟩:= Rhythm.buyE D (orderK V) _ p; exact ⟨S,D,E⟩
variable {u}(A:Prelude V u)
abbrev cap (A:Prelude V u) := min A.E.pre.limit A.E.H.calm
lemma cap_p : 0<A.cap V:=lt_min A.E.pre.legal A.E.H.caution
lemma horizon : ∃ e:ℕ,∀ a:ℕ,e ≤ a → Nonempty (Rhythm.Note A.E (Gates.gap P.L a) J.n):=by
 obtain ⟨n,h⟩:= eventually_atTop.mp (Rhythm.notes_p A.E (orderK V)); exact ⟨n, fun k p=> h _ (by unfold Gates.gap; omega) _⟩
end Prelude
-- Depth invariant: buy before h. can ask w0 arbitrary e.g. l_B of seplift*3. retains all h consumers and drift profiles.
variable {V u}
structure Profile (A:Prelude V u) where
 a : ℕ
 choice : 2*P.L.val ∣ a
 note : Rhythm.Note A.E (Gates.gap P.L a) J.n
 course : Mote A.S A.E note F W.C.b W.C.B
namespace Profile
variable {J}
lemma choose_a(J: Robes N V W)(A:Prelude V u) : ∃ e:ℕ,∀ a:ℕ, 2*P.L.val∣a→e ≤ a → ∃ H:Profile J A,H.a=a:=by
 obtain ⟨i,h⟩:= Prelude.horizon V J A; refine ⟨i,fun a w p=>?_⟩; obtain ⟨n⟩:= h a p; obtain ⟨v⟩:= Start.births A.S A.E n F (orderK V) _ _ W.C.posb W.C.posB.le; exact ⟨⟨a,w,n,v⟩,rfl⟩
lemma book(J: Robes N V W)(A:Prelude V u)(r:ℕ): ∃ H:Profile J A,r≤H.a:=by
 obtain ⟨i,h⟩:=choose_a J A; let l:= P.L; have hl:l.val>0:=l.property; let a:=2*l.val*(i+r); have hp:i+r≤a:=(by unfold a; nlinarith only [hl,mul_le_mul_of_nonneg_right (show 1≤l.val by omega) (show 0 ≤ i+r by omega)]) -- `<` shape use one
 obtain ⟨H,w⟩:=h a (dvd_mul_right ..) (by omega); exact ⟨H,w.symm ▸ le_trans (by omega : r≤ i+r) hp⟩
variable {A:Prelude V u}(Z:Profile J A)
def Height:= Oasis.coins Z.course.oak
lemma height_p :1≤Z.Height:=Oasis.coin_ge _
variable {h}
def Afford(x:ℝ):Prop:= ∀ y:ℝ,x≤y→ Nonempty (Z.course.Licence radiusB (Py.dleaf P.L) (Z.course.council radiusB y) y h)
lemma spends (p:Height Z≤ h): ∀ᶠ x:ℝ in atTop, Afford (h:=h) Z x:=by
 let W':= Z.course; obtain ⟨u,v⟩:= W'.council_pt _ pR; have he:= Mote.availability W' radiusB (dleaf P.L) u pR (dleaf_p _) v (Eventually.of_forall fun y=>Nat.le_add_right ..) (t_future _) h p W.health
 obtain ⟨z,f⟩:= eventually_atTop.mp he; filter_upwards [eventually_ge_atTop z] with x hp; exact fun y u=> f y (hp.trans u)
end Profile
end YM.CF.BProof.Diary
