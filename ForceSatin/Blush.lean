import ForceSatin.SunS
import ForceSatin.Canto
import YM.SU5.Circuit.Lark
set_option autoImplicit false
set_option maxHeartbeats 360000
noncomputable section
namespace YM.Gleam.Luster.Risa.Gentle.Solace
open Next.SectorChange Next.SectorChange.Gaussian Function Filter MeasureTheory Metric Finset RG Lattice Wilson Tree Precision Pressure Exterior Next.Rank.Spindle Work.F03 Fineness Regis ProbabilityTheory Module
open scoped Topology ContDiff BigOperators Classical ENNReal InnerProductSpace
open Regis.Head CF.Scree Push.Local Brecht
open Regis.Circuit Regis.Circuit.SpringDay
variable {c n:Side}{G:Gauge}{u v a C K σ η X:ℝ}{Z:PathData G}{B:Bed}{q:Clip}
variable (H:Z.Bounds q a C K)(P:Attached B Z)(L:Floor B q n η X)(p:B.covered σ X)(hp:0<σ)
lemma make_alt (x: ShapeLight G n): Sun H P 1 x=(↑(trill H P x.2 (x.1.1,plaquette x.1.2)):Altar G n):=by
 let g:= stamen H P n; let F:= trill H P x.2 (x.1.1,plaquette x.1.2)
 apply ext_inner_right ℝ; intro k
 let v:=g.orthogonalProjectionOnto k
 rw [Sun, cone]; rw [show inner ℝ (↑F:Altar G n) k= _ from ((Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (K:=g) F k)).symm]; unfold F; rw [Brecht.joy,inspire]; change 1* ((Etch.river q x.1 (_)) x.2)=_; rw [one_mul]; rfl
include p hp L
lemma crest_pledge (i j:ShapeLight G n)(v:Even n.val): (↑(inner ℝ (Sun H P 1 i) (Sun H P 1 j)):ℂ)=(Brecht.sch (G:=G) i.2 j.2:ℂ)*rimble n B (i.1.1,plaquette i.1.2) (j.1.1,plaquette j.1.2):=by
 rw [make_alt,make_alt]; have he:= chimes H P L p hp i.2 j.2 (i.1.1,plaquette i.1.2) (j.1.1,plaquette j.1.2) v; simp_rw [←Brecht.joy, Brecht.appraisal] at he; exact he
#check @Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
#print axioms crest_pledge
variable (v0:0<X)
open Regis.Circuit.SpringDay.Lyra CF.Onyx
omit p hp L in
lemma moonstone (B:Bed)(x y:Cover)(F D: PlaqAxes): rimble n B (wrap n x,plaquette F) (wrap n y,plaquette D)=skyPrice (rubyOff n) (fun i=> Cov B (rubyM i) (plaquette F) (plaquette D)) (x-y):=by rw [rimflare n B (wrap n x) (wrap n y) (x-y) (map_sub ..|>.symm)]; unfold skyPrice; rfl
omit p L
include v0
lemma asteroid (q:Clip)(η:ℝ)(F D: PlaqAxes)(l:List Cover):∃ C:ℝ, 0<C∧∀ n:ℕ→Side,∀ B:ℕ→Bed,Tendsto (fun i=>(n i).val) atTop atTop→ (∀ i,Floor (B i) q (n i) η X) → (∀ i,(B i).covered σ X) →(∀ i,Even (n i).val) → ∀ x:Cover,x≠0→∀ᶠ i in atTop,
    ‖muJet l (fun x:Cover=> rimble (n i) (B i) (wrap (n i) x,plaquette F) (0,plaquette D)) x-muJet l (specter F D ∘ scape) x‖ ≤ C/rally x^(5+l.length):=by
 obtain ⟨C,a,P⟩:= timely (hornPromise hp v0 q η (plaquette F) (plaquette D)) (Spring.hessianTrade F D) l; refine ⟨C,a,fun n B s L v e x g=>?_⟩; let z(i):crown q σ η X:=⟨n i,B i,L i,v i,e i⟩; have he:= P z (fun i=> juneC (n i) (e i)) s x g; refine he.mono fun i he=>?_; have ht(x':Cover): rimble (n i) (B i) (wrap (n i) x',plaquette F) (0,plaquette D)=warble (hornPromise hp v0 q η (plaquette F) (plaquette D)) (z i) x':=by have hf:=moonstone (n:=n i) (B i) x' 0 F D; rw [map_zero,sub_zero] at hf; exact hf
 rw [funext ht]; exact he
#print axioms asteroid
end YM.Gleam.Luster.Risa.Gentle.Solace
