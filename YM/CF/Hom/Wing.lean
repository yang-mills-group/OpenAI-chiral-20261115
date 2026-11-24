import YM.CF.Hom.Meso
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Hom
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Next.Free Pressure Cascade Reef
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {L B A m:Side}{ho:Odd L.val}{j k:ℕ}{a b d r s u v n X l η e:ℝ}{Y:Pricing j L ho (Thread j)}{P:Grasp Y B e}
section bounds
variable (K:Teller group)
def roseT (Q: Teller group):ℝ:= eta Q.C Q.C
lemma rose_y(p:1 ≤ K.C): 0<roseT K:=by
 have ht: 0<K.C:=zero_lt_one.trans_le p; haveI : Nonempty (TypeFace 2):= ⟨Exterior.plaquette ⟨(0,1),by decide⟩⟩; unfold roseT eta Extra.Iteration.psiPrice; positivity
variable {K}
lemma road_b{K:Teller group} {G: Ratio m A}{W:Flight K.j K.j}{X Z:Bed}{T:Towers W.L}{h:(More A).val=(More m).val*W.L.val}{F:Forest (W.visitRatio h)}{z:Cloud m→ AxisChart group F} (p:1≤ K.C)(H:Paddle W K.bind X Z K.top.clip T K.η K.C) (g:Nativity (T:=W.visit K.bind h) F z)(t:MainIn group K.top.clip X η K.η K.C)(v: MainIn group K.top.clip Z η K.η K.C) (y:Guessed (S:=W.visit K.bind h) F (Bloch.installed (W.visitRatio h) T.A0) z): Gazes (W.visit K.bind h) F z K.η K.C (roseT K):=by
 let S:=W.visit K.bind h; have hv:T.Deep K.η K.C 1:= ⟨H.pay.1, H.pay.2.1,H.pay.2.2.1,fun i hi=> H.pay.2.2.2 i (by have he:= W.legal; omega)⟩; have he:X.dual_diag.strip K.η K.C:=t.1.2.2.2.2; have hx: Z.diagonal.strip K.η K.C:=v.1.1
 exact Panels y g (produce1 S X Z T K.width he hx hv) K.width (zero_le_one.trans p) he hx hv (t.2.1 _) (H.link _)
lemma cover_u(k:ℕ)(K:Teller group)(J:RG.Patch) :∃ A B:ℝ,0<A ∧0<B ∧∀ {m r:Side}(T:RG.StepData (More m) (More r)) (F:Forest T.ratio){z:Cloud m→ AxisChart group F}(R:RG.PathData group), Bid.Larger (G:=group) T → T.kernel=K.bind → T.patch=J→ J.J=K.j→ ∀ l:ℝ,R.Bounds K.top.clip K.top.width K.top.paths l→ Critical F K.top.clip R z → Laic.Horizon F z k A B:=by
 obtain ⟨X⟩:= Push.Uniform.pre_order group K.top.width K.top.paths K.j K.bind (n:=k+3) (by omega)
 let B:= X.tables K.top.clip J; let a:= Push.Uniform.responseRate B.coords (k+3) B.value B.width B.gap; let b:= Push.Uniform.curveCost B.coords B.value B.width B.gap k
 refine ⟨if 0<a then a else 1,max b 1,by split; assumption; exact zero_lt_one,lt_of_lt_of_le zero_lt_one (le_max_right ..),fun {m r} T F {z} R p q e h t v u=>?_⟩
 obtain ⟨ht,hg,hk⟩:=provision X v p (e ▸ h) q (show k<k+3 by omega) u -- tune e.trans
 have hu: T.patch= _:= e
 subst J; rw [if_pos (show 0<a from hg)]; refine ⟨ht.1,ht.2,fun i hi g s t=>?_⟩; exact (ht.3 _ hi g _ _).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (Real.exp_pos _|>.le)) -- tune
end bounds
end YM.CF.Hom
