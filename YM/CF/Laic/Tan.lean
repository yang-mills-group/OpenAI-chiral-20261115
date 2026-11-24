import YM.CF.Laic.Shade
set_option autoImplicit false
noncomputable section
namespace YM.CF.Laic
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker
variable {m n A B X:Side}{k w:ℕ}{a b d h:ℝ}{T:RG.StepData (More n) (More X)}{F:Forest T.ratio}
abbrev Snap(F:Forest T.ratio):=Positions (Push.Uniform.Joint F SU.group)
def hats(F:Forest T.ratio)(x:Snap F):Nom n X:= (Push.Uniform.fine group F x, Push.Uniform.outer group F x)
lemma hats0:hats F 0=1:=by obtain ⟨p,w⟩:= paint_supply group 0; exact Prod.ext ((fine_supply F w).1) ((outer_supply F w).1)
section litG
open scoped Matrix.Norms.Frobenius
structure EnvM {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{n:Side}(N:ℕ)(F:E→ Bkg n)(x:E)(c:ℝ):Prop where
 ink(i): Allows N (fun y=> SU.group.mat (F y i)) x c
lemma hatch (k:ℕ):∃ A:ℝ,0≤A∧∀ {m n:Side}{T:RG.StepData (More m) (More n)}(F:Forest T.ratio), EnvM k (fine SU.group F) 0 A ∧ EnvM k (outer SU.group F) 0 A:=by
 obtain ⟨C,H⟩:=paint_supply group k; let U:=fineCost group k C; let V:= outerCost group k C; let Q:= max U V; refine ⟨Q, le_max_of_le_right (outer_pos _ _ H.1|>.le),fun F=> ⟨⟨fun i=> ((fine_supply F H).2.2 _ _ (by simp)).mono (le_max_left ..)⟩,⟨fun i=>((outer_supply F H).2.2 _ _ (by simp)).mono (le_max_right ..)⟩⟩⟩
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](u:E→Bkg n){p:E}(U:EnvM k u p a)
def entry_F(i j: Fin SU.group.repDim): SU.group.Mat→L[ℝ]ℂ:= (show SU.group.Mat→ₗ[ℝ]ℂ from ⟨⟨fun u=>u i j,fun _ _=>rfl⟩,fun _ _=>rfl⟩).toContinuousLinearMap
def normL {A B:Type*}[NormedAddCommGroup A][NormedSpace ℝ A][NormedAddCommGroup B][NormedSpace ℝ B](X:A→L[ℝ]B):=‖X‖
lemma normZ {A B:Type*}[NormedAddCommGroup A][NormedSpace ℝ A][NormedAddCommGroup B][NormedSpace ℝ B](X:A→L[ℝ]B):0≤normL X:=norm_nonneg _
def normA (A : SU.group.Mat→L[ℝ]ℂ):=normL (A:=group.Mat) A
def dGray (a:ℝ):= (∑ i:Fin group.repDim,∑ j:Fin group.repDim,normA (entry_F i j))*a
lemma pike(H:0≤a)(i j:Fin group.repDim): normA (entry_F i j)*a≤ dGray a:=by unfold dGray; apply mul_le_mul_of_nonneg_right _ H; exact le_trans (single_le_sum (f:=fun j=>normA (entry_F i j)) (fun _ _=>normZ (A:=group.Mat) _) (mem_univ j)) (single_le_sum (f:=fun x=>∑ j:Fin group.repDim,normA (entry_F x j)) (fun _ _=>sum_nonneg fun _ _=> normZ (A:=group.Mat) _) (mem_univ i))
lemma dGray_pos (h:0≤a):0≤ dGray a:=mul_nonneg (sum_nonneg fun _ _=>sum_nonneg fun _ _=> normZ (A:=group.Mat) _) h
include U
lemma delight (x)(i j:Fin SU.group.repDim): Allows k (fun y=> group.mat (u y x) i j) p (dGray a):=by have ht:= U.ink x; exact (ht.linear (entry_F i j) le_rfl).mono (pike ht.nonneg _ _)
end litG
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
lemma plex (k:ℕ)(h:0≤a):∃ c:ℝ,0≤c ∧∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{n:Side}{F:E→Bkg n}{x:E}, EnvM k F x a→ F x=1→ Allows k (fun i=> profile (F i)) x c:=by
 have he:0 ≤ dGray a:=by exact dGray_pos h
 have hp: ContDiffAt ℝ ω triple (fund 1):=by
   refine Nacre.tort.mpr ?_; rintro ⟨i,r⟩ ⟨j,s⟩; have he (i j:SU.F): ContDiffAt ℝ ω (fun p:Op SU.F=> p i j) (fund 1):=Nacre.tort.mp contDiffAt_id i j; refine ContDiffAt.mul contDiffAt_const ?_; cases r with -- copy
   | inl a=> cases s with
      | inl b=> change ContDiffAt ℝ ω (fun p=>SU.each p (.inl a) (.inl b)) _; simp_rw [each,Join.both,Matrix.fromBlocks_apply₁₁,ExTwo.wedge_entry]; exact ((he _ _).mul (he _ _)).sub ((he _ _).mul (he _ _))
      | inr b=> exact contDiffAt_const
   | inr a=> cases s with
      | inl b=> exact contDiffAt_const
      | inr b=> exact Complex.conjCLE.contDiff.contDiffAt.comp _ (he a b)
 obtain ⟨s,hs,g⟩:=exists_allows (s:={fund (1:SU.E)}) (isCompact_singleton) (f:=triple) (fun x hx=> Set.mem_singleton_iff.mp hx ▸ hp) k -- tune
 let X:= (coordL (k:=SU.F)).symm.toContinuousLinearMap; let v:= ‖X‖* dGray a; let o:=composeCost k s v; let b:=max o v; have hv:0≤v:=mul_nonneg (norm_nonneg X) he; have hb:0≤b:=hv.trans (le_max_right ..)
 let L:=(starL ℝ: Twig≃L[ℝ] Twig).toContinuousLinearMap
 refine ⟨b+‖L‖*b,hb.trans (le_add_of_nonneg_right (by positivity)),?_⟩; intro E _ _ n f x U w; have hh:0≤ b+‖L‖*b:=by positivity
 apply allows_pi hh; intro i; apply allows_pi hh; intro j
 let z(y):=fund (f y i); have hp: Allows k z x v:= (allows_pi he fun m:SU.F=>allows_pi he fun n:SU.F=> delight f U i m n).linear X le_rfl
 have he:z x∈({fund (1:SU.E)}:Set (Op SU.F)):=by simp only [z,w,Pi.one_apply,Set.mem_singleton_iff]
 have hz(v): brand (f v i) = (triple (z v), z v):=rfl -- defeq?
 have ht:Allows k (fun y=> brand (f y i)) x b:=by simp_rw [hz]; exact (((g _ he).comp hp).mono (le_max_left ..)).pair (hp.mono (le_max_right ..))
 cases j; exact (ht.linear L le_rfl).mono (le_add_of_nonneg_left hb); exact ht.mono (le_add_of_nonneg_right (by positivity))
end YM.CF.Laic
