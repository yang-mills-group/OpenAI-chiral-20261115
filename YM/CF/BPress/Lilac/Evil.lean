import YM.CF.BPress.Lilac.Leaf
/- real charges compare: keep exact home traces of real_, h & non-in-gap traces. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Lilac
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG Sugar Honey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Net Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Sugar.Stage Wealth Weave Pressure Mount.Silhouette Awards Push.SectorMeasure Env Scree Vesper Shot Crew Honey Honey.Recipe Peel Peel.Spine Ledger
variable {m s N:Side}{B:BandWidth}{A:Bands (More N) B}{R:Hangar (More N)} {X: Sugar.Stage N}{Y:Driver N}
open Bias Bias.Sails Shale Primary.Fare
variable (p:Born A R X Y)
namespace Born
local notation "V"=> Picks A R ∅
lemma diffReal (z:Fin 5): real_ (p.H₁ z) - real_ (p.H₁ 0)= p.tileF z:=by
 let Kz(z:Fin 5):= Rosetta z A X.W R X.tile 2; let hp(z:Fin 5):billZ (Stride.Locks V true) (Stride.Locks V false) (nativeX Y.j Y.M N) 0 (Paint.coupling (Kz z))= p.tileF z:=by unfold tileF Bias.fareF; rw [p.readK z]
 rw [p.real_b z,p.real_b 0]; unfold Shale.oxide; rw [hp z,hp 0,p.free_pay, add_zero]; abel
lemma ash_atNode (U: Op (Single N))(x:Site N): (homeX (U:=Y) U (node x)).re= Bias.ash x U:=by
 apply congrArg (Complex.re); unfold homeX Pf.Anchor.homeF; change (∑ i:Single N with node i.1.1=node x, _) = _; have h(i:Site N):node i=node x ↔ i=x:=Tenant.needle.eq_iff; simp_rw [h]; symm; unfold Matrix.trace; apply sum_bij (fun i _=> (((x,i.1),i.2):Single N)); · intro i p; simp
 · intro i u j v t; exact Prod.ext (Prod.mk.inj ((Prod.mk.inj t).1)|>.2) (Prod.mk.inj t).2
 · rintro ⟨⟨i,j⟩,k⟩ v; change ((i,j),k)∈ _ at v; have he:i=x:= (mem_filter.mp v).2; exact ⟨(j,k),mem_univ _, he ▸ rfl⟩
 intro i p; rfl
abbrev BiasQ (z:Fin 5)(x:Site (More N)) := (homeX (U:=Y) (p.tileF z) x).re
lemma posting(z:Fin 5)(x:Site (More N)): p.BiasQ z x≤0:=by have he:= Pf.Anchor.sign Y.Beta.stage (p.tileF z) x 0 (p.nonpos_t z); simpa [Anchor.homeF, BiasQ,homeX] using he -- maybe `_ type uninf`
lemma bask(z: Fin 5)(I:Pec.Pride N)(x: Site (More N)) : (Primary.Fare.town I (p.H₁ z) x).re-(Primary.Fare.town I (p.H₁ 0) x).re= p.BiasQ z x:=by
 have he(x:Op (Single N))(y z:Op (Single N))(h:x-y=z)(i):x i i-y i i=z i i:= congrFun (congrFun h i) i
 unfold Primary.Fare.town homeX Pf.Anchor.homeF BiasQ homeX Pf.Anchor.homeF; -- tune town ambiguous
 simp_rw [Complex.re_sum,Primary.stork,Matrix.sub_apply,Complex.sub_re,real_c,p.heG]; rw [←sum_sub_distrib]; apply sum_congr rfl; intro i _; simpa using congrArg Complex.re (he _ _ _ (p.diffReal z) i)
lemma deepPart (i:A.Index)(x:Site (More N))(v:x∈ deep A i X.W.M): ¬ NearBlock A X.W.M x:= (mem_filter.mp v).2 -- tune deeps
-- deep_M reference alignment. even for nonempty support coincidences.LabelC Θ
variable (i:A.Index)(z: Fin 5)
lemma turnD {U Vz W:Pledge}(h:Wish Y U Vz W): let g:Mach (More N):= fun x=> pivotal z A i; Plain.Along (deep A i X.W.M) (moveW (p.H₁ 0) h g).val (p.H₁ z).val:=by
 intro g; let S:=deep A i X.W.M; let η:= pivotal z A i; have ht(x)(h:x∈ S): RosettaX z A X.W R X.tile x= scaledV (g x) (RosettaX 0 A X.W R X.tile x) ∧ ∀ u:ℝ,Rosetta z A X.W R X.tile u x= swivelC (g x) (Rosetta 0 A X.W R X.tile u x) := Hazel.Zone.deep_s z (p.ideal z).progress (p.ideal 0).progress (deep_sub A i _ h) (deepPart i _ h) -- tune order
 refine ⟨fun j _ _=>?_,fun i h=> (ht i h).1.symm,fun i h=>rfl,fun x v k=>?_⟩; · change η*1*η⁻¹=(1:SU.E); group
 apply ContinuousMap.ext; intro t; cases k; exact ((ht x v).2 t.val).symm; exact (Hazel.Zone.d_swive _ _ (g x) _ _ (ht x v).2 (((p.ideal 0).progress.Ksmooth x).differentiable (by norm_num) t.val)).symm -- tune if z argument
end Born
end YM.CF.BPress.Lilac
