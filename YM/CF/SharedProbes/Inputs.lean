import YM.CF.Swell.VitaK
import YM.CF.Liss.Sir

/-! Original FiniteGaugeData source initialization, recombination, and the common vacuum reading. -/
noncomputable section
namespace YM.CF.SharedProbes

open Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Palot Cadre Vow Py
open RG Mew Rive Nor Hake Bake Rue Salt Leaf
open Metric Drapes Tulip Lat Branch Cube Tenant Hove Haro Hest Dial Proa Tye
open Prism Moto Oath Font Levier Rill
open Neon Hom Vale Vale.Grace Kea Nova RP RP.Str Spark Precision Next.Free Gauge
open Paige Vault Brace Spire Pressure Jade Oise
open scoped Classical Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra loreM loreN boreKSpace boreXN

variable {m B : Side} {A : Teller SU.group} {W : ChartRatio SU.group} {p : Patch}
  (D : Grace A p W) {d : ℝ} (V : GramM (mid m B)) (X : Grasp D.U B d)
  (U : Loom (mid m B))

/-- The unmarked operator inserted into the original FiniteGaugeData ket gives the vacuum denominator. -/
theorem unitNumerator :
    Liss.rider_V D (fun _ => (1 : FC (Single (mid m B)))) V X U =
      Scree.partitionZ V X U := by
  simp only [Liss.rider_V, Py.tallyT, act_one] <;> rfl

/-- Therefore the normalized unit reading is one wherever the actual vacuum is nonzero. -/
theorem unitReading (h : Scree.partitionZ V X U ≠ 0) :
    Liss.rider_V D (fun _ => (1 : FC (Single (mid m B)))) V X U /
      Scree.partitionZ V X U = 1 := by
  rw [unitNumerator, div_self h]

end YM.CF.SharedProbes
