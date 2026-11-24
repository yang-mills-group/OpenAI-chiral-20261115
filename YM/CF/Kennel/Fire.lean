import YM.CF.Kennel.Porch
set_option autoImplicit false
noncomputable section
namespace YM.CF.Kennel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font
section frost
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.Frobenius
lemma arq{X I:Type}[NormedAddCommGroup X][NormedSpace ℝ X](f:X→ I→SU.E)(x:X)(h:Stationary.Army (G:=group) f x)(p:I)(i j:Fin group.repDim): ContDiffAt ℝ ω (fun y=> group.mat (f y p) i j) x:=by
 let F:group.Mat→ₗ[ℝ] ℂ:=⟨⟨fun p=> p i j,fun a b=>rfl⟩,fun a b=>rfl⟩; exact F.toContinuousLinearMap.contDiff.contDiffAt.comp x (h p)
end frost
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m A B L:Side}{j:ℕ}{ho:Odd L.val}{d a b:ℝ}{n:ℕ}{G:Ratio (CSide m B) (CSide A B)}
variable (L j ho G) in
def crux(M:Male)(x:nomA m A B)(C:Op (Single (CSide A B))):=capT (foal j true M G (unionP x)) (foot G C) -- L ho not used declarations variable? remove
variable (L j ho G) in
def era (M:Male)(x:nomA m A B)(C:Op (Single (CSide A B))):= fruit L j ho G M x (crux j G M x C)
variable (L j ho G) in
def gate (M:Male)(x:nomA m A B)(C:Op (Single (CSide A B))):=desire L j ho G M x (crux j G M x C)
variable (L j ho G) in
def leftN (M:Male)(x:nomA m A B)(C:Op (Single (CSide A B))):=bentT (pine j L ho (Thread j) false M G (unionP x)) (wh j L ho false M G (unionP x)) (ticketT (Thread j) false M G (unionP x)) (-star (crux j G M x C))
lemma inv_p {N:Type*}[LinearOrder N][Fintype N]{R:Op N}(t:IsUnit R): ContDiffAt ℝ ω (fun S:Op N=> S⁻¹) R:=by
 obtain ⟨y,rfl⟩:=t; simp_rw [Matrix.nonsing_inv_eq_ringInverse]; exact contDiffAt_ringInverse ℝ y
lemma wind_q {X I: Type}[NormedAddCommGroup X][NormedSpace ℝ X](f:X→ I→ SU.E)(x:X)(h: Stationary.Army (G:=SU.group) f x)(z:I): ContDiffAt ℝ ω (fun y=> SU.group.mat (f y z)) x:=by
 exact Nacre.tort.mpr fun i j=>arq f x h z i j
lemma tundra {c d:Side}{X : Type}[NormedAddCommGroup X][NormedSpace ℝ X](f:X→ Nom c d)(x:X)(h:Stationary.Army (G:=SU.group) (fun y=> (f y).1) x)(hp:Stationary.Army (G:=group) (fun y=>(f y).2) x):ContDiffAt ℝ ω (fun y=> unionP (f y)) x:=by
 have he{N:Side}(f:X→Bkg N)(h:Stationary.Army (G:=SU.group) f x) : ContDiffAt ℝ ω (fun y=> profile (f y)) x:=by
    refine contDiffAt_pi.mpr fun i=> contDiffAt_pi.mpr fun j=>?_
    have hv:ContDiffAt ℝ ω (fun p=> brand (f p i)) x:= (Nacre.face_b x (fun p=>f p i) (wind_q f x h i)).prodMk (wind_q f x h i)
    cases j; exact (starL ℝ:Twig≃L[ℝ] Twig).contDiff.contDiffAt.comp x hv; exact hv
 exact (he _ h).prodMk (he _ hp) -- implicits
lemma chillQ {C : Type*}[NormedAddCommGroup C][NormedSpace ℝ C]{x:C→nomA m A B}{c:C→Op (Single (CSide A B))}(P:Spack j L ho a b d n)(hp:G.count=L)(p:n≤(CSide m B).val)(M:Male)(t:C)(k:ContDiffAt ℝ ω (fun y=> unionP (x y)) t)(h:ContDiffAt ℝ ω c t)(he:unionP (x t)∈legal G d): ContDiffAt ℝ ω (fun y=> crux j G M (x y) (c y)) t∧ ContDiffAt ℝ ω (fun y=> gate L j ho G M (x y) (c y)) t ∧ ContDiffAt ℝ ω (fun y=> leftN L j ho G M (x y) (c y)) t ∧ (‖gate L j ho G M (x t) (c t)‖<1 → ContDiffAt ℝ ω (fun y=> era L j ho G M (x y) (c y)) t):=by
 let H(y):= unionP (x y); let S:=H t
 have hz(V:Coil (CSide m B) (CSide A B)→Op (Iota G))(u v:Bool)(g:Crown (Drapes.badge _) (Peaks.parcel G u d) (Peaks.parcel G v d) a b (fun i=> V i.val)): ContDiffAt ℝ ω (V∘H) t:= (crown_air G g S ((Peaks.cabin ..).mem_nhds he)).comp (f:=H) t k
 let W:=ticketT (Thread j) true M G; let Z:= ticketT (Thread j) false M G; let Q:= foal j true M G; let B':=wh j L ho true M G; let U:=wh j L ho false M G; let K:=pine j L ho (Thread j) true M G; let N:=pine j L ho (Thread j) false M G
 have hw:= hz W _ _ (P.W M G hp p); have hh:= hz K _ _ (P.K M G hp p)
 have hu:= hz Z _ _ (P.A M G hp p); have hi:= hz Q _ _ (P.P M G hp p)
 have hv:= hz B' _ _ (P.U M G hp p); have hl:= hz N _ _ (P.H M G hp p)
 have ha : ContDiffAt ℝ ω (fun y=> foot G (c y)) t:= Nacre.tort.mpr fun _ _=> Nacre.tort.mp h _ _
 let T(y):= crux j G M (x y) (c y)
 have hg : ContDiffAt ℝ ω T t:= (((ContDiffAt.sub (f:=fun _=>1) contDiffAt_const hi).mul ha).mul hi)
 have hB : ContDiffAt ℝ ω (U∘H) t:=by
    rw [show U∘H = (fun y=> 1-B' (H y)) from funext fun y=> wh_neg j L ho G true M (H y)]; exact contDiffAt_const.sub hv
 let f(y):=gate L j ho G M (x y) (c y); have hy:ContDiffAt ℝ ω f t:=(hh.mul (hv.mul hw)).mul hg
 have hk: ContDiffAt ℝ ω (fun y=> leftN L j ho G M (x y) (c y)) t:=(hl.mul (hB.mul hu)).mul (((starL ℝ: Op (Iota G) ≃L[ℝ] Op (Iota G)).contDiff.contDiffAt.comp t hg).neg)
 refine ⟨hg,hy,hk,fun p=>?_⟩
 have hx:ContDiffAt ℝ ω (fun y=> (1+f y)⁻¹) t:= (inv_p (close_c p)).comp (f:=fun y=> 1+f y) _ (contDiffAt_const.add hy)
 have hw:ContDiffAt ℝ ω (fun y=> traitP (B' (H y)) (K (H y)) (W (H y)) (T y)) t:=((contDiffAt_const.sub hv).mul (hw.mul (contDiffAt_const.add hg))).mul (hx.mul hh)
 exact Nacre.tort.mpr fun _ _=> Nacre.tort.mp hw _ _
end YM.CF.Kennel
