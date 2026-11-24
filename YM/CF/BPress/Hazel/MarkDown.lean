import YM.CF.BPress.Hazel.Harbor
import YM.CF.BPress.Hazel.Tonic
/- N collar amendment. Before any activation taper. Uniform costs across depth- & parameter change. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Hazel
open Function Finset Filter NormedSpace Metric SU SU.Pair Lat Fock Lattice Cube Spin Spin.Paint Dial Lute Lute.Kite Lute.Fort Lute.Music Meadow MeasureTheory Net Meadow.Tent Sheet
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {s :Side}{B:BandWidth}{u v γ : ℝ} (z: Fin 5)
open Grid Wealth Tunnel Locale Bands Branch Clipγ
variable (X:Bands s B)(W:Rental)(R:Hangar s)(S:Seal (SiteX X R))
private def tMin (T:Support s)(x:Site s)(p:T.Nonempty):ℕ := T.inf' p (separation x)
private lemma tHits(T:Support s)(x:Site s)(p:T.Nonempty):∃ i ∈ T, tMin T x p=separation x i:= Finset.exists_mem_eq_inf' p _
private lemma tLess(T:Support s)(x:Site s)(p:T.Nonempty)(y:Site s)(h:y∈T): tMin T x p ≤ separation x y:= inf'_le _ h
-- Eq:B-taper. remains uniform and purchases finite halo. exact dependence needed also in mapping of $H_v^*$ even on various assemblies.
def blink (x:Site s):ℝ:= if h:(Danger X R W S).Nonempty then gamma W.T (tMin _ x h) else 1
lemma between (x:Site s): blink X W R S x∈ Hotel:=by unfold blink; split; exact lit ..; exact H1
variable {X W R S}
lemma tAlive {x:Site s} (p:x∉ halo W.T.val (Danger X R W S)): blink X W R S x=1:=by
 unfold blink; split; next h=> apply Clipγ.full; obtain ⟨t,q,H⟩:= tHits _ x h; by_contra! e; exact p (halo_spec.mpr ⟨_,q,(separation_comm ..).le.trans ((H.symm ▸ e).le)⟩) -- tune
 next h=> rfl
lemma tTurnZero {x:Site s}{u:ℕ}(p:x∈ halo u (Danger X R W S))(t:u*8 ≤W.T.val) : blink X W R S x=0:=by obtain ⟨y,v,h⟩:=halo_spec.mp p; rw [blink,dif_pos (show _ from ⟨_,v⟩),Clipγ.dark ((Nat.mul_le_mul_right 8 ((tLess _ x _ y v).trans (by rw [separation_comm]; exact h))).trans t)] -- tune
lemma tSee {S T: Seal (SiteX X R)}{x:Site s}(p:∀ y∈halo W.T.val {x}, y∈ Danger X R W S ↔ y∈ Danger X R W T) : blink X W R S x= blink X W R T x:=by
 have ht:∀ u,W.T.val≥ u→ (x∈halo u (Danger X R W S)↔ x∈halo u (Danger X R W T)):= by
    intro u t; have he(y:Site s)(h:separation y x≤u):y∈halo W.T.val {x}:= halo_spec.mpr ⟨x,mem_singleton_self _,(separation_comm ..).le.trans (h.trans t)⟩; rw [halo_spec,halo_spec]; exact exists_congr (fun i=> and_congr_left (fun g=> p i (he i g)))
 by_cases h:x∈halo W.T.val (Danger X R W S); swap; · rw [tAlive h,tAlive (mt (ht _ le_rfl).mpr h)]
 let A:=Danger X R W S; let B:=Danger X R W T; have he (V:Support s)(n:V.Nonempty)(j:ℕ): x∈halo j V ↔ tMin V x n≤j:=by rw [halo_spec]; constructor; rintro ⟨v,u,t⟩; exact (tLess _ _ n _ u).trans ((separation_comm ..).le.trans t); intro t; obtain ⟨a,v,g⟩:= tHits _ x n; exact ⟨_,v,by rw [separation_comm,←g]; exact t⟩
 obtain ⟨i,v,_⟩:=halo_spec.mp h; obtain ⟨j,z,_⟩:=halo_spec.mp ((ht W.T.val le_rfl).mp h); have e:A.Nonempty:=⟨i,v⟩; have f:B.Nonempty:=⟨j,z⟩; let l:=tMin A x e; let t:=tMin B x f; have hp:l≤ W.T.val:=(he A e _).1 h; have hq:t≤W.T.val:=(he B f _).1 ((ht W.T.val le_rfl).1 h); unfold blink; rw [dif_pos e,dif_pos f]; change gamma W.T l=gamma W.T t; rw [show l=t from (by refine le_antisymm ((he A e t).1 ((ht t hq).2 ((he B f t).2 le_rfl))) ((he B f l).1 ((ht l hp).1 ((he A e l).2 le_rfl))))] -- tune
lemma t_rate (X:Bands s B)(R:Hangar s)(V:Rental)(T:Seal (SiteX X R))(l:Link s) : |blink X V R T l.1 - blink X V R T (endAt l)| ≤ chk V.T:=by
 unfold blink; split; next h=>
   let A:=Danger X R V T; have he (x y)(t:separation x y≤1): tMin A x h ≤ tMin A y h +1:= by obtain ⟨z,q,H⟩:= tHits _ y h; rw [H]; apply (tLess _ _ h _ q).trans; apply (separation_triangle _ y _).trans; omega
                                                                                                                                                                                                                                                                                                                                                                -- indent
   exact γ_neigh (he l.1 (endAt l) (Lat.oneTouch ..)) (he (endAt l) l.1 ((separation_comm ..).le.trans (Lat.oneTouch ..)))
 next h=> rw [sub_self,abs_zero]; unfold chk; positivity
end YM.CF.BPress.Hazel
