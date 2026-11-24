import YM.CF.Py.Chime
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vale
open Function Filter Lattice Laurent Bloch Wilson Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Next.Free Pressure Cascade Reef Hom PhysicalNext.JointLoad.Heir
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {K:Teller group}{P:RG.Patch}{R:ChartRatio group}{W:Postal}{η e:ℝ}{n k v i:ℕ}{f g a b d w:ℝ}{B m c u:Side}{C:Credit}
variable {U: Pricing K.j P.L P.odd_side (Thread K.j)} {D:Grasp U B e}{S:Gold K P R W}{x y z:ℝ}
open Grace
lemma Month.fitX(n k j:ℕ)(hp:6 ≤ n)(ht:2 ≤ k)(V:Grace K P R){X:Grasp V.U B e}(G:GivenX V X): ∀ᶠ x in atTop,∀ r:ℝ,0<r→ ∃ T:Month x r n k j V G,T.q=G.n+(100+j)*(1+Pressure.radiusB (hat P.L x 0)):=by
 filter_upwards [fates n k hp ht P.L,mastK P.L,eventually_ge_atTop (2*G.z)] with x ha hz hx r hr
 obtain ⟨A,H,Y⟩:=ha r hr
 let u:=1+radiusB (hat P.L x 0); let q:= G.n+ (100+j)*u; have hh: G.n≤ q:=by unfold q; omega
 refine ⟨⟨A,q,hh,fun i=>?_,Y,fun {m} v i t=>?_, fun {m} v i F P=>reach P (G.pose _ i) hx (by linarith [G.hp]) V.roomZ G.hp.le,fun {m} v i=> Gold.Last.station_room (G.arm ..) (G.pose (hh.trans v) i) hx V.roomZ G.hp.le⟩,rfl⟩
 · grind
 let h':=(100+j); have he:(100+j)* (1+radiusB (hat P.L x t)) ≤ (cell m B P.L t).val:= bulk_size x h' t (by have h:=V.tallX; omega) hz ((by unfold q h'; omega : h'*u≤q).trans v)
 have hX: G.n ≤ (cell m B P.L t).val:= hh.trans (v.trans (amplit ..)); let E:= kint m B P.L t
 refine ⟨V.L.cert i E ?_ _ ?_, V.L.seamL ..,?_⟩
 · change V.W.n ≤ (cell m B P.L t).val*2; have hv:= G.flag; omega
 · refine ((Nat.mul_le_mul_right _ (Nat.le_add_right 100 j)).trans he).trans ?_; change (cell m B P.L t).val ≤ (cell m B P.L t).val*2; omega
 rw [(H t).2.2.2.1]; exact (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)).trans he
end YM.CF.Vale
