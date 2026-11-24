import YM.CF.Pec.Breath
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n X m A L B :Side}{j k w:ℕ}{ho:Odd L.val} {Y:Pricing j L ho (Thread j)}{e d b a r:ℝ}{P:Grasp Y B e}
variable {G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B}{F: Forest T.ratio}{z:Vox m B→ AxisChart group F}
variable (H:Hull j L ho a b d e k m A B G T F z Y P)
def lush (G:Ratio (CSide m B) (CSide A B))(P:Grasp Y B e)(M: Male)(U:Dress (CSide A B)) (x:nomA m A B):ℂ:= -(altar G P x M)-invoice (coatG L ho j G M U x)
include H
lemma glacier (V:nomA m A B→ ℂ)(u:∀ᶠ i in 𝓝 (0:Vox m B),∀ g:Site (More (CSide A B))→E,V (july G g (ears F z i))= V (ears F z i)): Vale (V∘ ears F z) :=by
 have ht {x y:ℝ→ Vox m B}(g:Tendsto x (𝓝 0) (𝓝 0))(t:ℝ→Site (More (CSide m B))→ E)(hp:∀ᶠ s:ℝ in 𝓝 0, ∃ g: Site (More (CSide A B))→E,g ∘ T.ratio.embed=t s∧ baby F z (y s)=Lattice.gauge g (baby F z (x s)))(he: ∀ᶠ s:ℝ in 𝓝 0, represent (y s)= Lattice.gauge (t s) (represent (x s))):∀ᶠ s:ℝ in 𝓝 0, V (ears F z (y s))=V (ears F z (x s)):=by
    filter_upwards [g.eventually u,hp,he] with i hl ⟨u,v,p⟩ he
    have hx:scaleG G u=t i:=by unfold scaleG; rw [←H.alignT]; exact v
    rw [show ears _ _ (y i)=july G u (ears _ _ (x i)) from Prod.ext p (by rw [←hx] at he; exact he)]
    exact hl u
 constructor; intro g x; exact ht (Hull.ray_home x) (fun _ _=>g) (H.native.mirrors g x) (Eventually.of_forall fun s=> orderD ..)
 intro x r; exact ht (Hull.ray_home x) _ (H.native.shower r x) (wraps ..)
lemma fame(M:Male)(K:Pearl P) :∀ x,JointB G x e→∀ g:Site (More (CSide A B))→E, altar G P (july G g x) M= altar G P x M:=by
 obtain ⟨c,v,hC,hV,D⟩:= pollen 0 K H.stamp H.hi H.above; obtain ⟨Z,hz,Q⟩:= D m A G H.fromL H.size_p M F H.alignT; intro x g p; rw [Q _ g,Q _ (joint_g G x g p)]; refine sum_congr rfl fun i _=>hz.gauge i p x g
lemma paidP(M:Male)(U:Dress (CSide A B))(v:Ample U):∀ᶠ x in 𝓝 0,∀ i:Site (More (CSide A B))→E, let Z:=ears F z x; coatG L ho j G M U (july G i Z)= twist ((Peaks.parcel G true d).run i) (coatG L ho j G M U Z):=by
 filter_upwards [H.native.melod d H.po G, H.nickP M v.self] with x hx he i Z
 unfold coatG; rw [show (july G i Z).1=_ from (rfl : _ = Lattice.gauge i Z.1),v.ripe]; exact (Dusk H.tape G M H.fromL H.request Z (ambient _ _ H.po le_rfl hx) i (U Z.1) he.1).2
lemma nyc (M:Male)(U:Dress (CSide A B))(p:Ample U)(K:Pearl P){X X':ℝ→ Vox m B}(f:Tendsto X (𝓝 0) (𝓝 0))(a:Shape)(h:∀ᶠ s in 𝓝 0, ∃ g:Site (More (CSide A B))→E,g ∘ (ratio G).embed=1 ∧ baby F z (X' s)= Lattice.gauge g (Yg (a.broad G) (baby F z (X s))))(l:∀ᶠ s in 𝓝 (0:ℝ), represent (X' s)=Yg a (represent (X s)))(v:∀ x:Bkg (More (CSide A B)), U (Yg (a.broad G) x)= ZoneH (a.broad G) (U x)): ∀ᶠ s in 𝓝 (0:ℝ), lush G P M U (ears F z (X' s))= pays a.s (lush G P M U (ears F z (X s))):=by
 filter_upwards [h,l,f.eventually (H.native.melod e H.hi G),f.eventually (H.native.melod d H.po G), f.eventually (H.nickP M p.self)] with s hs hy hu hv ht; obtain ⟨g,r,R⟩:=hs
 let x:=ears F z (X s); let V:=U (baby F z (X s)); let t:=scaleG G g; let y:=stanza G a inert x; have he: ears F z (X' s)=july G g y:= Prod.ext R (show _=_ from hy.trans (by change y.2= Lattice.gauge t y.2; rw [show t=1 from r,Stationary.gauge_one]))
 let Z:=ZoneH (a.broad G) V; obtain ⟨Hq,Hx,Hz⟩:= duelX H.above H.hi H.stamp H.fromL H.size_p hu (H.tape.tape _ H.fromL H.request M (unionP x) (ambient _ _ H.po le_rfl hv)) V a _ rfl ht.1 ht.2
 unfold lush; rw [he, fame H M K y (alongS inert a G x e hu) g]
 have hq: altar G P y M=pays a.s (altar G P x M):=by
    have hx:= chain_sym K H.stamp H.size_p H.above G H.fromL H.hi x hu M a false; rw [complX]; simp only [Bool.false_xor] at hx; exact hx -- tune inert def
 rw [map_sub,map_neg,hq]; apply congrArg (-(pays a.s) (altar G P x M)-·)
 have hl:V=U x.1:=rfl
 have hG:=Dusk H.tape G M H.fromL H.request y (ambient _ _ H.po le_rfl (alongS inert a G (ears F z (X s)) d hv)) g Z Hz
 change invoice (gate L j ho G M _ (U (Lattice.gauge g y.1)))= _; rw [p.ripe, show y.1=Yg (a.broad G) x.1 from rfl,v]
 change invoice (gate L j ho G M _ (ActZ g Z))=pays a.s (invoice (gate L j ho G M x V))
 rw [show gate L j ho G M _ _= twist ((Peaks.parcel G true d).run g) (gate L j ho G M y Z) from hG.2,bill_invariant _ (gate L j ho G M y Z) Hz, complX]; exact Hx
lemma nycR (M:Male)(U:Dress (CSide A B))(p:Ample U)(K:Pearl P)(x:Vox m B): let g:=lush G P M U ∘ ears F z; (∀ t,∀ᶠ s:ℝ in 𝓝 0, g (s • SubMotion t x)=g (s • x)) ∧∀ v,∀ᶠ s:ℝ in 𝓝 0,g (s • litX v x)=pays v (g (s • x)):=by
 intro g; constructor
 · intro t; let y(u:ℝ):=u • SubMotion t x
   have ht:∀ᶠ s:ℝ in 𝓝 0, represent (y s)=Yg (lagX t) (represent (s • x)):= Eventually.of_forall fun s=>height ..
   have hp:= nyc H M U p K (Hull.ray_home x) (lagX t) (H.native.translation (x:=fun s:ℝ=> s • x) (y:=y) (by fun_prop) (zero_smul ..) (by unfold y; fun_prop) (zero_smul ..) H.alignT t ht) ht (fun x=> p.across _ _) -- tune
   filter_upwards [hp] with i hi; change lush _ _ _ _ _= _; rw [show lush G P M U (ears F z (i • _))=_ from hi,complX]; simp only [lagX]; rw [show detX 1=false by have hp:=det_p 1 1; rw [one_mul,Bool.xor_self] at hp; exact hp]; rfl
 intro v; let y(s:ℝ):=s • litX v x; have he:∀ᶠ s:ℝ in 𝓝 0,represent (y s)=Yg (incX v) (represent (s • x)):= Eventually.of_forall fun s=>(roomy ..).symm
 exact nyc H M U p K (Hull.ray_home x) (incX v) (H.native.slash (x:=fun s:ℝ=> s • x) (y:=y) (by fun_prop) (zero_smul ..) (by unfold y; fun_prop) (zero_smul ..) H.alignT v he) he (by rw [show (incX v).broad G=incX v from ?_]; exact p.plane v; simp [incX,Shape.broad])
end YM.CF.Pec
