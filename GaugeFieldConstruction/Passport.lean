import GaugeFieldConstruction.Sodality
import YM.SU5.FiniteGaugeData.Tapestry.Junction
import YM.SU5.FiniteGaugeData.Tower.Flood
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale
variable {Λ: Preparation} {l : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l))
variable (s i k:ℕ)(p:Satin.PairIdx Y s i k)
local notation "σ" => side Y i s
local notation "nP"=> (Λ.Ctor (Y.ir i) (s+1))
local notation "Z"=> ((Y.voyage i).X (Y.uv k))
local notation "G"=> (Vale.apt (Y.ir i) Λ.block Λ.R.L s)
local notation "ΦA"=> steps Λ.V (Y.ir i) Λ.block (Y.uv k) s
local notation "C" => (Y.voyage i).CapeT
local notation "Zg"=> patternGram Y i k
abbrev flyer (x:Orbit σ)(y:Orbit nP) := lynx Λ.K ΦA G (C (s+1)) (C (s+1)) (C s) ((Z).gram (s+1)) Chi.canonical Λ.J.d (patternQ Y s i k).val x y
abbrev Hally (f:Orbit nP→Phys nP)(x:Orbit σ): Phys σ:=∫ y, (flyer Y s i k x y) (f y) ∂city _
include p
lemma devote {f:Orbit nP→Phys nP}(h:Envelope f){b:Bool}{u:Finset (Seat σ)}{U:Mark σ}(t:AtSupport b u U): markedRead U (C s) (Hally Y s i k f)= markedRead (ascender Y s i k U) (C (s+1)) f:=by
  have a:=(fullness Y i k p.1).cap_grant; obtain ⟨L⟩:= a.grant s p.2
  exact passport G L ΦA (patternQ Y s i k) Λ.R.odd_side (a.branch s p.2) h (Journey.legal Λ) t
-- Devote all even test supports wear along track.
omit p
local notation "c₀"=> reserve Λ l
local notation "Lamₐ"=> distanceLaw l
local notation "al"=> aliasLaw Λ
local notation "L₀"=> Λ.R.L.val
abbrev framesM (U: Finset (Seat σ)):= padded G U (L₀*gross al Lamₐ Λ.R.J)
-- Budget supports use torus wrap. Doesn't require a common-axis separation.
-- no macro notation in section bindings.
include p
lemma Hank {S:Finset (Seat σ)} {b:Bool} {f:Mark σ}(h: AtSupport b S f): AtSupport b (framesM Y s i S) (ascender Y s i k f):=by
 have a':=(fullness Y i k p.1).cap_grant; obtain ⟨L⟩:= a'.grant s p.2; obtain ⟨_,_,_,V',_⟩:=L.cap
 have h':= surround G ΦA Λ.K.j (patternQ Y s i k).val ((Z).gram (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d ((Z).gram (s+1)).beta (C s) (Journey.legal _) V'.bill (a'.branch s p.2) L.legal.1 L.legal.2 _ h (Journey.tissue Y i s) (a'.aligned s p.2)
 have eq: (patternA Y s i k).patch.J=Λ.R.J:= a'.radius s p.2; rw [eq] at h'; exact h'
omit p
abbrev WardEnd(S U: Finset (Seat σ)):Prop:= ∀ x∈S,∀ y∈U, 2*c₀<separation x y
lemma profits {S U}(h:WardEnd Y s i S U): WardEnd Y (s+1) i (framesM Y s i S) (framesM Y s i U):=by
 intro x px y py; obtain ⟨i',v,e⟩:= halo_spec.mp px; obtain ⟨j',w,p'⟩:= halo_spec.mp py
 obtain ⟨l₀,h₀,rfl⟩:=mem_image.mp v; obtain ⟨r₀,h₁,rfl⟩:= mem_image.mp w
 have h': L₀*(2*c₀)<L₀* separation l₀ r₀:= Nat.mul_lt_mul_of_pos_left (h _ h₀ _ h₁) Λ.R.L.property
 have hv:L₀* separation l₀ r₀ ≤ separation ((ratio G).embed l₀) ((ratio G).embed r₀) := Corona.below (ratio G) l₀ r₀
 have he:= separation_triangle ((ratio G).embed l₀) x ((ratio G).embed r₀); have hi:= separation_triangle x y ((ratio G).embed r₀)
 have hy:separation y ((ratio G).embed r₀)≤L₀*gross al Lamₐ Λ.R.J := (separation_comm ..).trans_le p'
 have hx:separation ((ratio G).embed l₀) x≤L₀*gross al Lamₐ Λ.R.J:= e
 have hw:c₀+1+L₀*gross al Lamₐ Λ.R.J≤ L₀*c₀:= Tower.width_margin Λ l
 rw [show L₀*(2*c₀)=2*(L₀*c₀) from by ring] at h'; omega
include p
lemma AirMag {S U}{b c : Bool}{f g:Mark σ} (h:AtSupport b S f) (t: AtSupport c U g) (u:WardEnd Y s i S U): ascender Y s i k (f*g)= ascender Y s i k f * ascender Y s i k g:=by
 have he:=(fullness Y i k p.1).cap_grant; obtain ⟨L⟩:= he.grant s p.2; obtain ⟨_,_,_,V',_⟩:=L.cap
 apply separated_mult G ΦA Λ.K.j (patternQ Y s i k).val _ Λ.R.odd_side Chi.canonical Λ.J.d ((Z).gram (s+1)).beta (C s) (Journey.legal Λ) V'.bill (he.branch s p.2) L.legal.1 L.legal.2 _ _ h t (Journey.tissue Y i s)
 intro x hx y hy; refine lt_of_le_of_lt (Nat.mul_le_mul_left 2 ?_) (u x hx y hy)
 rw [show c₀=16*(100*L₀*(1+al)+Lamₐ+Λ.R.J+10)+1 from by unfold Journey.reserve r₃ r₁; ring]; have ha:=Λ.R.coarse; change 3≤L₀ at ha
 unfold nearZero; nlinarith
end YM.CF.Buffered.Afterglow.Tapestry
end
