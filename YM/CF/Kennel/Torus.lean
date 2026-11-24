import YM.CF.Kennel.Cask
set_option autoImplicit false
noncomputable section
namespace YM.CF.Kennel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Hull
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N P:Side}{k:ℕ}{m A B L:Side}{j:ℕ}{ho:Odd L.val}{d a b:ℝ}{n:ℕ}
variable {e:ℝ}{G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B}{F:Forest T.ratio}{z:Vox m B→ AxisChart group F}{Y:Pricing j L ho (Thread j)}{V:Grasp Y B e}
-- keep separate since abstract with CL before plugs
structure Gazes {m y:Side}(T:RG.StepData (More m) (More y))(F:Forest T.ratio)(z:Cloud m→AxisChart group F)(a s K:ℝ):Prop where
 was:∃ Λ, Rails T.ratio K a Λ ∧ ∀ i:Site (More y),∀ j:Site (More m),∃ h:PrizeX y→ PrizeX m→ℝ,SweepH Λ h s ∧ ∀ x: Cloud m, let f:= fderiv ℝ (Iteration.chartOf F z) 0;∀ k, heat i (collect group (f x)) k=∑ t,h k t • heat j (collect group x) t
lemma Panels{c d:Side}{T:RG.StepData (More c) (More d)}{F:Forest T.ratio}{z:Cloud c→AxisChart group F}{P Q:Bed}{U:Towers T.patch.L}{α B a s v:ℝ}(g: Guessed F (installed T.ratio U.A0) z)(f:Nativity F z)(h:Rails T.ratio s v (lambda (S:=T) P Q U))(p:0<a)(r:0≤α)(he:P.dual_diag.strip a α)(hf:Q.diagonal.strip a B)(t:U.Deep a α 1){y:RG.Clip}{β:ℝ}(H:Floor P y (More d) β B)(K:Towers.Diagonal T P Q U):Gazes T F z v α s:=by
 obtain ⟨_,_,_,_,_,_,_,hx,_⟩:= f.was; refine ⟨_,h,fun i j=>?_⟩; obtain ⟨Y,G,L⟩:= bowl (G:=group) F i j p r he hf t H K; refine ⟨Y,G,?_⟩; intro u h k; rw [show h u=_ from Iteration.chart_tangent z hx g u]; exact L u k
lemma bud_inc {S:Ratio N P}{F:Matrix (Single P) (Single N) ℂ}{a b d:ℝ}(p:BudH S F a b)(h:d≤a): BudH S F d b:=by
 have he(x y): bolt d S x y*‖F x y‖≤ bolt a S x y*‖F x y‖:=by unfold bolt; gcongr
 exact ⟨fun x=> le_trans (sum_le_sum fun y _=> he x y) (p.stem _),fun y=> le_trans (sum_le_sum fun x _=> he x y) (p.hip y)⟩
lemma Rails_inc {G:Ratio N P}{a b d:ℝ}{Λ}(p: Rails G a b Λ)(h:d≤ b): Rails G a d Λ:=by
 have he(x y:Site N)(i j:ℝ):Faro d x y* ‖i‖ ≤ Faro b x y* ‖i‖:=by unfold Faro; gcongr
 cases p with | mk rate shot => exact ⟨fun i=>le_trans (sum_le_sum fun j _=>he _ _ _ 0) (rate i),fun i j=> le_trans (sum_le_sum fun k _=>he _ _ _ 0) (shot i j)⟩ -- shape inspect
variable (M:Male)
namespace Hull
variable (H:Hull j L ho a b d e n m A B G T F z Y V) (U:Dress (CSide A B))(p:relic U){J:Toy k (CSide A B)}(q: handy J)(v:Prints J)(w:0<k)
include H q v p w
lemma attica {X:Toy k (CSide m B)}{u Bv:ℝ}(h:∀ x:Vox m B,pyre X x=gallery L j ho G M (pyre J (fderiv ℝ (Iteration.chartOf F z) 0 x)))(hB:∀ i,balance u X i≤ Bv):∃ C:Toy k (CSide m B),Prints C ∧ handy C∧ Nacre.crystal k ((emergence L j ho G F z M (U+sumU (cavil J))) - emergence L j ho G F z M U) (spurTx C) ∧∀ i,balance u C i ≤ Bv*sugarK:=by
 let L':= (CSide A B); let f:= gallery L j ho G M; let R:= fderiv ℝ (Iteration.chartOf F z) 0; let U':=cavil J; let T:=emergence L j ho G F z M; have hk:= relic_r k w J; have hz: Across U':=fun t i=> pre_a _ _ _ v -- syntax
 have hg := H.glen M (p:=hk.1) (cobblestone _ q) hz; have hy:= H.glen (U:=0) M relic_zero (ripZ U') (fun t i=> (map_zero _).symm)
 have hx: Nacre.crystal k (T U'-T 0) (pyre X):=by
    rw [show U'= 0+U' from (zero_add _).symm,show pyre X=f ∘ pyre J ∘ R from funext h]; exact H.breach M (U:=0) relic_zero k hk.1 _ (H.crownJ hk.1 _ fun i=> peak_e i J)
 obtain ⟨C,B,Q,A,K⟩:=lit X (tiltL (glazeM hg hy) hx); refine ⟨C,Q,B,?_, K _ _ hB⟩
 have ht:= H.breach M p k hk.2.1 _ (H.crownJ hk.2.1 _ fun i=> priced i J); intro x; unfold spurTx; rw [←A]; simp_rw [h]; have hh(i:Signed): f (ZoneH (incX i) (pyre J (litX i⁻¹ (R x))))=ZoneH (incX i) (f (pyre J (R (litX i⁻¹ x)))):=H.decor M J q w i x
 have hp:=ht x; change Tendsto _ _ (𝓝 (f (spurTx J (R x)))) at hp; unfold spurTx at hp; rw [map_smul,map_sum] at hp; simp_rw [hh] at hp; exact hp
end Hull
end YM.CF.Kennel
