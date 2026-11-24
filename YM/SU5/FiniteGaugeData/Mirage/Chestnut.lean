import YM.SU5.FiniteGaugeData.Mirage.Faint
import YM.SU5.FiniteGaugeData.Mirage.Dune
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 440000
noncomputable section
namespace YM.CF.Window.Mirage
open Function Filter Lattice Cube Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
open Scroll Spire Peaks Tap Tenant Tulip Buffered Fock.Brique Window.Brique Largo
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
variable {N X:Side}{s r d w j:ℕ}{a C:ℝ}{σ τ:Window.Family}{S T U:Finset Cover}
local notation "Μ"=> Single N
local notation "Κ"=> FC (Single N)
open SU Dial Cascade Scree Skye Branch Paige
variable (L:Mark N→ₗ[ℂ]ℂ)
section
-- native pair when elected. plus.Fock. frame global on R, restricts left/right, global constant left (invariant on every field). right E cov after orbit avg. support names.
variable {o1 o2: Seat N}{U V P D1 D2 E1 J :Support (More N)} (F1:Corset U D1 o1)(F2:Corset V D2 o2) (F: Corset P J o2)
abbrev FineT (U: Support (More N)):= Reed.Fine (Tset N) (modesIn N U) false
def Already (A:FC (Single N)):= ∀ u:SU.E, orbitB A u=A
variable {W:Pane N→ℂ}(hF:Stump J W)(p:U∪V ⊆ P)(u:P⊆J)(pF:P⊆ J)
structure Frame : Prop where
 left(a:Pane N): ∃ v:SU.E, Set.EqOn (F.g a) (globalH N v*F1.g a) U
 right(a:Pane N): Set.EqOn (F.g a) (F2.g a) V
variable (TTT:Frame F1 F2 F)
include TTT
lemma Frame.mesh (A B:FC (Single N))(x:FineT U A)(X:Already A)(g:FineT V B): conspire F (A*B)= (conspire F1 A*conspire F2 B):=by
 funext i; change cargo _ 1 _ i= cargo _ 1 _ i * cargo _ 1 _ i
 let a:= i.1; let H:= F.g a; let H':= F2.g a; obtain ⟨v,t⟩:= TTT.left a; let K:= globalH N v; let H0:= F1.g a; unfold cargo; change 1 • flipsP H⁻¹ (A* B) = (1:ℂ) • flipsP H0⁻¹ A *((1:ℂ) • flipsP H'⁻¹ B)
 simp only [one_smul,map_mul]; rw [flips_s (H')⁻¹ H⁻¹ V (by intro i x; rw [Pi.inv_apply,Pi.inv_apply]; exact congrArg Inv.inv (TTT.right _ x).symm) g.sector, flips_s (K*H0)⁻¹ H⁻¹ U (by intro i x; rw [Pi.inv_apply,Pi.inv_apply]; exact congrArg Inv.inv (t x).symm) x.sector, mul_inv_rev,wind_join, ←prop_global_i, show flipsP (globalH N v⁻¹) A=A from X _]
omit TTT
variable {d:ℝ} {Z:Peg N}(O:Casing N Z.e (Z.Ft false) a C d) -- d is ℕ cast! want d:ℝ shadow
variable {W':Loom N}{w f t t' θ:ℝ} -- w unused
variable (O':0≤Z.e)(A:CashMask F W E1 (d*t) W') -- remove
abbrev canv (F:Pane N→ℂ): Mark N:= fun i=> F i.1 • 1
variable {d':ℕ}{M:Tulip.Male}
variable (q:Z.Ft false 1=funde 4 M N 1)
-- now NOTE: require SMALL mask and UNMASKED distinction. `Insure` takes any Fine etc including care (`Mask native`). L actually extends E restricted.Balance. route. user witness. Left location & right additionally bounds.WIDTH. inputs from Two Duet Suites with costs elected.C.
variable (e:P ⊆ J) (u1:U⊆ P)(u2:V⊆P)(y:Lattice.halo d' P ⊆ E1)(g:E1⊆ J)(z₀:U ⊆ D1)(z₁:V⊆D2) {C1 C2 n:ℝ}{K K':ℕ}
local notation "P₀"=> fun (S:Finset Cover)=> (S.image (wrap N)).image node
abbrev twinCost(c1:ℝ)(n:ℕ):ℝ:= (1+c1)^(n*45*4)
structure Insure (N:Side)(L:Mark N→ₗ[ℂ]ℂ)(J E1: Support (More N))(Z: Peg N)(W': Loom N) (W:Pane N→ℂ)(d K:ℕ)(a b C:ℝ) :Prop where
 masked (A B:Mark N): AtSupport false J B → (∀ i,‖B i‖≤ C) → AtSupport false J A → (∀ i,‖A i‖≤ C) → (∀ x, B (Advance.drawn W' x)=A (Advance.drawn W' x)) → Crater d a b Z J B K false → ‖L A‖ ≤ 1/4
 uncovered (X:Mark N): AtSupport false J X → (∀ i,‖X i‖≤ C) → ‖L X-L (canv W*X)‖ ≤ 1/4
 unit : L 1=1
-- pickup EXACT same cutoff.Marker chooses Lft & Rgt species mix. for right distinct.The meaning of parameters c1 c2 height. `grow Norm ≤ Cc` with sectors.
lemma loomStitch (W:Pane N→ℂ)(A:FC (Single N)): cargo F W A=canv W * conspire F A:=by funext i; unfold cargo; simp only [Pi.mul_apply,canv]; rw [Algebra.smul_mul_assoc,one_mul]; rw [show (conspire F A) i=(1:ℂ) • flipsP (F.g i.1)⁻¹ A from rfl, one_smul]
include TTT O O' A q e u1 u2 y g z₀ z₁
variable {A1 A2 B1 B2: Finset Cover}
local notation "Θ"=> twinCost C1 K'*twinCost C1 K'
lemma Insure.bouquet (R:Insure N L J E1 Z W' W d' K t' θ (twinCost C1 K'*twinCost C1 K'))
 (P₁:Suite K N M S A1 B1 C1 C2 n)(P₂:Suite K N M S A2 B2 C1 C2 n)
 (U₁: (A1.image (wrap N)).image node⊆U)(V₁:(B2.image (wrap N)).image node⊆U)
 (U₂:(A2.image (wrap N)).image node⊆V)(V₂:(B1.image (wrap N)).image node⊆V) (TTT₁:(S.image (wrap N)).image node⊆P)
 (v:0≤t') (x:2*n+(2*tailCost a C d'+t*C)≤ θ-t')
 (u:A1.card≤K')(u':A2.card≤K')(v':σ.2=τ.2)(tκ:σ.1≠τ.1):
 ∃ f k:Mark N, Free D1 f ∧ Free D2 k ∧ covariant f ∧ covariant k ∧ discord L f k≠0 ∧ ∃ t:List (Site N),t≠[]∧ (∀ v,t.count v≤2) ∧ t.toFinset⊆ A2.image (wrap N) ∧ ∀ v, Chord σ τ N ((B1.image (wrap N)).image node) t (k v):=by
 -- Choose τ left & σ right
 obtain ⟨X1,Xl,XZ,h,y1⟩:= P₁.choice; obtain ⟨X2,Xr,YZ,s,y2⟩:=P₂.choice
 let β:=τ.1; let α:=σ.1;  -- remove
 let Vσ:=genre σ; let Y':=genre τ; have hk:Vσ=Y':=by unfold Vσ Y' genre; rw [v'];
 obtain ⟨b,p⟩:= paid_any σ; have hp:b∈ Vσ:=p; have hz:b∈ Y':=hk ▸ hp; let V':= ({b}:Finset Sheet); have hh:b∈ V':= mem_singleton_self _; have hv:V'⊆Vσ:= singleton_subset_iff.mpr hp
 let Ff:= eMark X1 Xr Y' β α; let G:= eMark X2 Xl V' α β
 let K0:= (piggy (WalU N A1) Y' β); let K1:=(piggy (WalU N A2) V' α)
 have hf(z:ℂ): Receipt τ σ ((B2.image (wrap N)).image node) K0 (Ff z-1):= R_shape h s v'.symm (Ne.symm tκ) Y' le_rfl z; have hq(z:ℂ): Receipt σ τ ((B1.image (wrap N)).image node) K1 (G z-1):= R_shape s h v' tκ V' hv z
 have helf (z:ℂ): Already (Ff z):= fun u=> pMount _ _ _ _ -- tune
 have hKi(j:Μ)(a:j∈ K1): j.1.1∈ Finset.image _ A2:= (mem_product.mp (mem_product.mp a).1).1
 have hF(z:ℂ): FineT U (Ff z-1):= (hf z).veil U V₁ (fun i t=> U₁ (mem_image_of_mem _ (mem_product.mp (mem_product.mp t).1).1)); have hG(z:ℂ): FineT V (G z-1):=(hq z).veil V V₂ (fun i t=> U₂ (mem_image_of_mem _ (hKi i t)))
 have h0:0≤ C1:= (norm_nonneg _).trans h.budget
 have hu(b:ℂ)(m:‖b‖=1):∀ x:SU.E, ‖Ff b* orbitB (G (star b)) x‖ ≤ (Θ) :=by
    have hh(Q:Finset Cover)(u: Q.card≤K')(p: Finset Sheet)(t:p.card≤45)(α:Fin 3): (piggy (WalU N Q) p α).card ≤ K'*45*4:=by
        refine le_trans (pinW _ Q p α ?_ t) (le_of_eq (mul_right_comm K' 4 45)); unfold WalU WalP; rw [card_product]; apply Nat.mul_le_mul (card_image_le.trans u) (by decide)
    have hx:‖Ff b‖ ≤ twinCost C1 K':= (E_cost h s β α (Ne.symm tκ) Y' b m).trans (pow_le_pow_right₀ (le_add_of_nonneg_right h0) (hh _ u _ genre_sum _)); have hp:‖G (star b)‖ ≤ twinCost C1 K':= (E_cost s h α β tκ V' _ ((norm_star ..).trans m)).trans (pow_le_pow_right₀ (le_add_of_nonneg_right h0) (hh _ u' V' (by simp only [V',card_singleton]; decide) _))
    exact fun x=> (norm_mul_le ..).trans (mul_le_mul hx ((twist_norm ..).trans_le hp) (norm_nonneg _) ((norm_nonneg _).trans hx)) -- second order norm_n?
 have hhAgainst (i:ℂ) (z:‖i‖=1)(W0:SU.E): ‖L (conspire F1 (Ff i)*conspire F2 (orbitB (G (star i)) W0))‖ ≤ 1/2:=by
   let c:=orbitB (G (star i)) W0; let K2:=Ff i * c
   let B:= cargo F W K2; let b':=conspire F K2; have he: FineT U (Ff i):=sub_add_cancel (Ff i) 1 ▸ ((hF i).add .one); have hx : FineT V (orbitB (G (star i)) W0) := windFine (globalH _ _) (sub_add_cancel (G (star i)) 1 ▸ ((hG (star i)).add .one))
   have Fk:FineT P K2:=(homes_cash _ _ he u1).grow (homes_cash _ _ hx u2)
   have hw:‖K2‖≤ (Θ):= hu i z W0; have hr:Free J B:= delivered F A.faces e Fk; have ht1:star i*i=1:=by simp [Complex.star_def, ← normSq_eq_conj_mul_self, normSq_eq_norm_sq,z]
   let tθ:= sunSat h s β α (Ne.symm tκ) Y' V' b hz hh i z ht1 P TTT₁ y1 y2; let Hmar:= Marble.rightRoom O O' W0 (Ff i) (G (star i)) (q.symm ▸ tθ : Marble (Z.Ft false 1) P K (Ff i* G (star i)) (2*n)) (helf i _)
   let hU(x):= (cargo_bound F A.faces K2 x).trans hw; have hΘ:= R.masked B _ (cared_area B hr g) (fun i=>(cared_cost B E1 i).trans (hU i)) hr.zone hU (fun x=>(stampEq A K2 x).symm.symm) (Mirage.paid_copy O A Hmar y O' v x g); let hV:= R.uncovered b' (delivered F (abrupt J) e Fk).zone (fun i=> (cargo_bound F (abrupt J) K2 i).trans hw)
   rw [show B= _ from loomStitch F W K2] at hΘ; have hz: b'= conspire F1 (Ff i)*conspire F2 (orbitB (G (star i)) W0):= TTT.mesh F1 F2 F _ _ he (helf i) hx -- tune args
   change ‖L (conspire F1 (Ff i) * conspire F2 _)‖≤_; rw [←hz]; change ‖L (canv W*b')‖ ≤ _ at hΘ; linarith only [hΘ,hV,norm_sub_norm_le (L b') (L (canv W*b'))] -- _ in change
 obtain ⟨z,vJoy,tZ,pZ,qZ,uZ,Cz,cz,Sz,Tz⟩:= against L F1 F2 τ Ff G (E_D h s v'.symm (Ne.symm tκ) _) (E_D s h v' tκ _) R.unit (E_zero h s β α (Ne.symm tκ) Y') (E_zero s h α β tκ V') hhAgainst K1 ((B1.image (wrap N)).image node) hq
 let Y:=spotted tZ; have hf': Y.toFinset⊆ A2.image (wrap N):= fun i t=> by obtain ⟨j,u,rfl⟩:= List.mem_map.mp (List.mem_toFinset.mp t); exact hKi j (uZ (List.mem_toFinset.mpr u));
 let hr:= hF z; let hv': FineT V Cz:= cz.fines (fun i t=> U₂ (mem_image_of_mem _ (hf' (List.mem_toFinset.mpr t)))) V₂ -- V₂ maybe!
 refine ⟨_,_,delivered F1 (abrupt D1) z₀ hr,delivered F2 (abrupt D2) z₁ hv', cargos F1 (abrupt D1) (Ff z-1) (fun i=>?_), cargos F2 (abrupt D2) Cz Tz,Sz, Y,?_,pigment_one _ b uZ qZ,hf',fun i=>(cz.wind _).mul _⟩
 · rw [map_sub,map_one, show flipsP _ (Ff z)=_ from helf z i]
 exact mt List.map_eq_nil_iff.mp pZ
end
end YM.CF.Window.Mirage
