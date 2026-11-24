import YM.CF.Vale.Archer
import YM.CF.BPress.Age.Neon

/- Adapted from FiniteGaugeData proofs in corresponding imported modules. Strengthening as in VolumeB-gate:
   keep q_P lower speed in same grant emitted while d, threshold still adjustable. This version is for
   B-main and any ordinary `MeterQ`, independent of comparison uses. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vale
open Function Filter Lattice Laurent Bloch Wilson Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Next.Free Pressure Cascade Reef Hom PhysicalNext.JointLoad.Heir
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {K:Teller group}{P:RG.Patch}{R:ChartRatio group}{W:Postal}{η e:ℝ}{n k v i:ℕ}{f g a b d w:ℝ}{B m c u:Side}{C:Credit}
variable {U: Pricing K.j P.L P.odd_side (Thread K.j)} {D:Grasp U B e}{S:Gold K P R W}{x y z:ℝ}
lemma spicesP(X:Grace K P R)(T:Acorn.Repair K.j)(z:ℕ): ∃ i:ℕ, z≤ i ∧ ∀ j:ℕ,i≤j → ∃ e u:ℝ,0< u∧0<e∧∀ x:ℝ,0<x →x≤ e →∃ D:Grasp X.U (P.L^j) x,(∃ V:Pearl D,V.q=u) ∧ x ≤ T.d ∧ D.baseline ≤ T.d ∧ T.n ≤D.roundZ:=by
 have he:= X.tallX; let L:=P.L; have ht:L.val≥2:=by unfold L; omega
 obtain ⟨N,H⟩:= avaP X.U T (by have hx:=X.L.lobby; have hy:=P.order_cut; omega); let b:=L^N; obtain ⟨n,h⟩:= H b (huge L ht _); let u:= L^n; obtain ⟨k,U⟩:= h u (huge L ht _); refine ⟨z+N+n+k,by omega,fun j hi=>?_⟩
 obtain ⟨e,u,hu,hT,A⟩:= U (L^j) ((by omega : k ≤ j).trans (huge L ht j)) ⟨L^(j-N),show L^j=L^N*_ from by rw [←pow_add]; congr; omega⟩ ⟨L^(j-n),show L^j=L^n*_ from by rw [←pow_add]; congr; omega⟩; refine ⟨e,u,hu,hT,fun x y z=>?_⟩
 obtain ⟨D,h,-,g,w⟩:= A x y z; exact ⟨D,h,g,w⟩
namespace Grace
variable{V:Grace K P R}{X:Grasp V.U B e}
lemma blessedP (p:Pearl X)(t:0<e):∃ H:GivenX V X,H.pearl=p:=by
 obtain ⟨C,h1,h2,h3,h4,F⟩:= V.aura p t; obtain ⟨z,u,i,H⟩:= sum_cost V.up V.gate V.note V.sp p V.a_o V.b_o V.d_o t V.tallX V.L C
 let N:=i+C.i+V.W.n; let a(m: Side)(p:N≤ m.val)(v:ℕ): V.L.Last X C m v:= Classical.choice (V.L.gives F (show C.i ≤ m.val from by unfold N at p; omega) v)
 exact ⟨⟨C,h1,h2,h3,h4,z,u,N,by unfold N; omega,p,t,F,fun {m}=>a m,fun {m} p k=> H (show i ≤ m.val from by unfold N at p; omega) k (a m p k)⟩,rfl⟩
end Grace
open Grace
-- A complete unbounded schedule of stationary services (not yet an RG step identity).
lemma scoreP(j n k:ℕ)(p:4 ≤ j)(h:Even j)(hp:6 ≤ n)(ht:2 ≤ k):∃ (K:Teller group) (Z:ChartRatio group), LocalRatio Z∧1 ≤ K.C∧K.j=j∧K.top.clip.direct ≤ 1∧(∀ P:RG.Patch, P.Branches K.bind group)∧ ∃ N:ℕ,∀ (P:RG.Patch),N ≤ P.L.val →P.J=j → ∃ (V:Grace K P Z)(T:Acorn.Repair K.j)(i:ℕ),∀ B:ℕ,i ≤ B→∃ e u:ℝ,0<u∧0<e ∧∀ y:ℝ,0<y → y≤ e →∃ (X:Grasp V.U (P.L^B) y)(G:GivenX V X), G.pearl.q=u ∧ y ≤ T.d∧ X.baseline ≤ T.d∧ T.n ≤ X.roundZ ∧∀ u:ℕ,∀ᶠ b:ℝ in atTop,∀ r:ℝ,0<r→Nonempty (Month b r n k u V G):=by
 obtain ⟨Z,Y⟩:= LocalH.actual group; obtain ⟨K,hK,z,u,w,N,H⟩:= sun j p h Z Y
 refine ⟨K,Z,Y,z,hK,u,w,N,fun P x t=>?_⟩; obtain ⟨F⟩:=H P x t; obtain ⟨D⟩:=Acorn.restoreX K.j (by omega); obtain ⟨i,h',v⟩:=spicesP F D 1
 refine ⟨F,D,i,fun B p=>?_⟩; obtain ⟨e,u,g,w,f⟩:=v B p; refine ⟨e,u,g,w,fun y z q=>?_⟩; obtain ⟨D',⟨P,hP⟩,a,b,c⟩:= f y z q; obtain ⟨R,T⟩:=blessedP P z
 exact ⟨D',R,T.symm ▸ hP,a,b,c,fun i=> Month.existsX n k i hp ht F R⟩
end YM.CF.Vale


