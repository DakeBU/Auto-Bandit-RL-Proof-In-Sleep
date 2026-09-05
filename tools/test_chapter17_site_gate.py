"""Keep the corrected Chapter 17 publication fence declaration-complete."""

import unittest

from website.scripts import build_site


class Chapter17SiteGateTests(unittest.TestCase):
    names = (
        "gaussianRandomPseudoRegret_ge_theorem17_1",
        "gaussianRandomPseudoRegret_ge_corollary17_2",
        "noUniformGaussianRandomPseudoRegretTail_corollary17_3",
        "exists_cdfTail_ge_of_integral_ge",
        "integrable_adversarialTableRandomRegret",
        "adversarialNoiseHistoryJoint_history_marginal",
        "adversarialNoiseHistoryJoint_pull_le_half_claim17_6",
        "adversarialFullBoundaryCount_tail_claim17_7",
        "adversarialFullRandomRegret_ge_boundary_eq17_8",
        "adversarialTable_strictTail_eq_one_sub_CDF",
        "adversarialRandomRegret_ge_theorem17_4",
    )

    def setUp(self):
        self.spine = {
            "canonical_source": {
                "official_url": build_site.PRIMARY_TEXTBOOK_URL,
                "doi": "10.1017/9781108571401",
            },
            "chapters": [
                {"number": n, "slug": str(n), "status": "partial", "pdf_page": 1}
                for n in range(13, 18)
            ],
        }
        self.index = {"BanditRLProof.LowerBounds." + name: {} for name in self.names}

    def test_corrected_chapter17_requires_complete_body_interfaces(self):
        self.spine["chapters"][-1]["status"] = "compiled"
        build_site.validate_textbook_spine(self.spine, self.index)

    def test_each_missing_body_interface_keeps_chapter17_fenced(self):
        self.spine["chapters"][-1]["status"] = "compiled"
        for name in self.index:
            with self.subTest(name=name):
                incomplete = dict(self.index)
                del incomplete[name]
                with self.assertRaisesRegex(ValueError, "cannot be promoted"):
                    build_site.validate_textbook_spine(self.spine, incomplete)

    def test_other_future_chapters_remain_fenced(self):
        for chapter in self.spine["chapters"][1:4]:
            with self.subTest(chapter=chapter["number"]):
                chapter["status"] = "compiled"
                with self.assertRaisesRegex(ValueError, "cannot be promoted"):
                    build_site.validate_textbook_spine(self.spine, self.index)
                chapter["status"] = "partial"


if __name__ == "__main__":
    unittest.main()
