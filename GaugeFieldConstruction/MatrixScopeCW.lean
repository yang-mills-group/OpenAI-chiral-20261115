import GaugeFieldConstruction.ExactScopeCW
/-!
# Price per raw m in the advertised chart dictionary
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.U1.TableDictionary
open Finset Function Raw Cauchy Row Certificate Vouchers Labels Chart
open scoped BigOperators Matrix
abbrev Pleg (a:Pol) := a.val.mom
abbrev gxy (a:Surface) (b:Wed) := area (Pleg a.1) (a.1.val.vel a.2) b.toBlade.val.1 b.toBlade.val.2
abbrev grain (x y:Surface) k := Pleg x.1 k+Pleg y.1 k
abbrev rod (x y:Pol) k := Pleg x k+Pleg y k
abbrev spur (x y:Pol) k := Pleg y k-Pleg x k
abbrev wakeM (x y:Pol)(z:Surface) k:= rod x y k+Pleg z.1 k

abbrev hWord (x y:Pol) (i : Axis) := ∑ a : Spin, ∑ b : Spin, x.val.pol false a * Hij i a b * y.val.pol true b
lemma fCore (x y:Pol)(i : Axis): fChart (x,y) (B i) = hWord x y i:=by
 rw [B,map_sum]; apply Finset.sum_congr rfl; intro a _; rw[map_sum]; apply Finset.sum_congr rfl; intro b _
 rw [map_smul, smul_eq_mul,fChart, read_times]; dsimp only; simp [ef,Weyl.read_C,power,fermi]; ring
lemma gPays (x:Surface)(a: Wed): eg x (arc a)=gxy x a:=by
 unfold arc eg; rw [wedge_formula]; simp [gxy,power,Pleg]
lemma gPiv (x y:Surface)(i : G4): gChart (x,y) (evalTg i)=
    gxy x i.val.1*gxy y i.val.2+gxy y i.val.1*gxy x i.val.2:=by
 rw [evalTg, gChart, bose_charge]; simp only [gPays]; ring
lemma kWdg (x:Surface)(i)(a: Wed): eg x (Gder i (arc a))= Pleg x.1 i*gxy x a:=by
 change (x.1.val.face x.2).read (Gder i (arc a)) = _
 rw [←LinearMap.comp_apply, (x.1.val.face x.2).frequency]; change Pleg x.1 i * eg x (arc a) = _
 rw[gPays]
lemma gPiv' (x y:Surface)(i:G5): gChart (x,y) (evalG i)=gxy x i.1*gxy y i.2.1*Pleg y.1 i.2.2+ gxy y i.1*gxy x i.2.1*Pleg x.1 i.2.2:=by
 rw [evalG,gChart,bose_charge]; simp only [gPays,kWdg]; ring
lemma fSum (x y:Pol)(i) (a:J f): fChart (x,y) (P_f i a) = rod x y i * fChart (x,y) a:= LinearMap.congr_fun (ph_charge i (x.val.fermi false) (y.val.fermi true)) a
lemma gSum (x y:Surface)(i)(a:J g): gChart (x,y) (P_g i a) = grain x y i * gChart (x,y) a:= LinearMap.congr_fun (ge_charge i (x.1.val.face x.2) (y.1.val.face y.2)) a
lemma xSum (s t:Pol)(u: Surface)(i)(a:J x): xChart ((s,t),u) (P_x i a)= wakeM s t u i * xChart ((s,t),u) a:= LinearMap.congr_fun (x_charge i (s.val.fermi false) (t.val.fermi true) (u.1.val.face u.2)) a
lemma fDif (x y:Pol)(i)(a:J f): fChart (x,y) (L i a) = spur x y i * fChart (x,y) a:=LinearMap.congr_fun (l_charge i (x.val.fermi false) (y.val.fermi true)) a
lemma fPiv (x y:Pol)(a:F4): fChart (x,y) (evalTf a)= hWord x y a.1 * a.2.elim (spur x y) (rod x y):=by
 rcases a with ⟨u,i|j⟩
 · exact (fDif ..).trans (by rw[fCore]; exact mul_comm ..)
 exact (fSum ..).trans (by rw[fCore]; exact mul_comm ..)
lemma fPiv' (x y:Pol)(a:F5): fChart (x,y) (evalF a)= hWord x y a.1 *
      a.2.elim (fun i=>spur x y i.val.1 * spur x y i.val.2) (Sum.elim
          (fun i=>rod x y i.val.1 * rod x y i.val.2) (fun z=>rod x y z.1*spur x y z.2)):=by
 rcases a with ⟨u,i | i| i⟩ <;> simp only [evalF,Sum.elim_inl, Sum.elim_inr,fSum,fDif,fCore] <;> ring
lemma xPiv (x y:Pol)(s:Surface)(i:X5): xChart ((x,y),s) (evalX i)= hWord x y i.1 * gxy s i.2:=by
 rw [evalX,xChart,read_times]; simp only [gPays,fCore]
-- Spending from orbit impulses: full output arrays, multiplied POM (pay same at all readings incl i-j.
variable {O Q S U β : Type*} (C:S→J U→ₗ[ℂ]ℂ)
lemma chart_formula [Fintype Q][DecidableEq Q][DecidableEq O](A:Labels Q)(D:Labels O)(q:Q→J U)(s) (j)(i:O) : photo C O (Record.dot q (payment A D s)) j i = ∑ b:Q, payment A D s (b,i)*C j (q b):=by
 change C j (Record.dot _ _ _) = _; rw[Record.dot_apply,map_sum]; simp[map_smul]
-- Canonical derivative contraction uses all i,j components, not just i<=j.
variable (R:Record U β)(pom:S→ Axis→ ℂ)(h: ∀ s k x, C s (R.P k x)=pom s k * C s x)
include h
lemma dot_there (t: Raw.Sym → J U) (s) (j): photo C Axis (R.divP t) s j=∑ i:Axis,pom s i * photo C _ t s (ordered i j):=by
 change C s (R.divP t j)=_; rw[Record.divT,map_sum]; exact Finset.sum_congr rfl fun i _=>h ..
lemma dot_go (t: Axis → J U)(s)(j k) : photo C (Axis×Axis) (R.heatP Axis t) s (j,k) = pom s j * photo C _ t s k:= h ..
lemma dot_here (t: VS → J U) (s) (j k): photo C (Axis×Axis) (R.divA t) s (j,k)=∑ i:Axis,pom s i * photo C _ t s (j,ordered i k):=by
 change C s (R.divA t (j,k))=_; rw [Record.divV,map_sum]; exact Finset.sum_congr rfl fun i _=>h ..
end YM.GaugeFieldConstruction.U1.TableDictionary
