/* RefParse, the algorithm for parsing lists of bibliographic references.
 * Copyright (C) 2011-2013 ViBRANT (FP7/2007-2013, GA 261532), by G. Sautter
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */
package de.uka.ipd.idaho.plugins.bibRefs.refParse;

import java.awt.BorderLayout;
import java.awt.Color;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.Reader;
import java.io.Writer;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Properties;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.swing.DefaultComboBoxModel;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JPanel;

import de.uka.ipd.idaho.gamta.Annotation;
import de.uka.ipd.idaho.gamta.AnnotationUtils;
import de.uka.ipd.idaho.gamta.Gamta;
import de.uka.ipd.idaho.gamta.MutableAnnotation;
import de.uka.ipd.idaho.gamta.StandaloneAnnotation;
import de.uka.ipd.idaho.gamta.TokenSequence;
import de.uka.ipd.idaho.gamta.TokenSequenceUtils;
import de.uka.ipd.idaho.gamta.util.AbstractConfigurableAnalyzer;
import de.uka.ipd.idaho.gamta.util.AnalyzerDataProvider;
import de.uka.ipd.idaho.gamta.util.AnnotationFilter;
import de.uka.ipd.idaho.gamta.util.AnnotationPatternMatcher;
import de.uka.ipd.idaho.gamta.util.AnnotationPatternMatcher.AnnotationIndex;
import de.uka.ipd.idaho.gamta.util.AnnotationPatternMatcher.MatchTree;
import de.uka.ipd.idaho.gamta.util.AnnotationPatternMatcher.MatchTreeNode;
import de.uka.ipd.idaho.gamta.util.CountingSet;
import de.uka.ipd.idaho.gamta.util.DocumentStyle;
import de.uka.ipd.idaho.gamta.util.DocumentStyle.ParameterGroupDescription;
import de.uka.ipd.idaho.gamta.util.DocumentStyle.PropertiesData;
import de.uka.ipd.idaho.gamta.util.ProgressMonitor;
import de.uka.ipd.idaho.gamta.util.ProgressMonitor.CascadingProgressMonitor;
import de.uka.ipd.idaho.gamta.util.analyzerConfiguration.AnalyzerConfigPanel;
import de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel;
import de.uka.ipd.idaho.gamta.util.feedback.html.FeedbackPanelHtmlRenderer.FeedbackPanelHtmlRendererInstance;
import de.uka.ipd.idaho.gamta.util.feedback.html.renderers.AnnotationEditorFeedbackPanelRenderer;
import de.uka.ipd.idaho.gamta.util.feedback.html.renderers.BufferedLineWriter;
import de.uka.ipd.idaho.gamta.util.feedback.panels.AnnotationEditorFeedbackPanel;
import de.uka.ipd.idaho.gamta.util.imaging.ImagingConstants;
import de.uka.ipd.idaho.plugins.bibRefs.BibRefConstants;
import de.uka.ipd.idaho.plugins.bibRefs.BibRefTypeSystem;
import de.uka.ipd.idaho.plugins.dateTime.DateTimeUtils;
import de.uka.ipd.idaho.plugins.properNames.ProperNameUtils;
import de.uka.ipd.idaho.plugins.properNames.ProperNameUtils.NameStyle;
import de.uka.ipd.idaho.stringUtils.Dictionary;
import de.uka.ipd.idaho.stringUtils.StringIterator;
import de.uka.ipd.idaho.stringUtils.StringVector;
import de.uka.ipd.idaho.stringUtils.regExUtils.RegExUtils;

/**
 * Source-wise singleton data container and utility class for the RefParse
 * bibliographic reference parsing algorithm.
 * 
 * @author sautter
 */
public abstract class RefParse extends AbstractConfigurableAnalyzer implements BibRefConstants, ImagingConstants {
	
	private static final String VOLUME_DESIGNATOR_TYPE = VOLUME_DESIGNATOR_ANNOTATION_TYPE;
	private static final String ISSUE_DESIGNATOR_TYPE = ISSUE_DESIGNATOR_ANNOTATION_TYPE;
	private static final String NUMBER_DESIGNATOR_TYPE = NUMERO_DESIGNATOR_ANNOTATION_TYPE;
	private static final String FASCICLE_DESIGNATOR_TYPE = "fascicle";
	private static final String SERIES_DESIGNATOR_TYPE = "series";
	
	public static final String GOT_FEEDBACK_ATTRIBUTE = "_gfb";
	private static final String NO_BIB_REF_ATTRIBUTE = "_nbr";
	
	private static final String AUTHOR_LIST_ANNOTATION_TYPE = "authorList";
	private static final String EDITOR_LIST_ANNOTATION_TYPE = "editorList";
	private static final String PAGE_RANGE_ANNOTATION_TYPE = "pageRange";
	private static final String NEXT_REFERENCE_ANNOTATION_TYPE = "nextRef";
	
	private static final String VOLUME_REFERENCE_ANNOTATION_TYPE = "volumeRef";
	private static final boolean integrateVolumeRefs = true;
	
	private static final boolean detailOrigin = false;
	
	private static final boolean DEBUG = true;
	
	private static final boolean DEBUG_STRUCTURE_SCORING = (DEBUG && true);
	
	private static final boolean DEBUG_AUTHOR_NAME_EXTRACTION = (DEBUG && true);
	private static final boolean DEBUG_AUTHOR_LIST_ASSEMBLY = (DEBUG && true);
	
	
	private HashMap highlightAttributeCache = new HashMap();
	private Color getAnnotationHighlight(String type) {
		Color color = ((Color) this.highlightAttributeCache.get(type));
		if (color == null) {
			if (AUTHOR_ANNOTATION_TYPE.equals(type))
				color = Color.ORANGE;
			else if (EDITOR_ANNOTATION_TYPE.equals(type))
				color = FeedbackPanel.darken(Color.ORANGE);
			else if (TITLE_ANNOTATION_TYPE.equals(type))
				color = FeedbackPanel.brighten(Color.GREEN);
			else if (VOLUME_TITLE_ANNOTATION_TYPE.equals(type))
				color = Color.GREEN;
			else if (YEAR_ANNOTATION_TYPE.equals(type))
				color = Color.RED;
			else if (JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE.equals(type))
				color = Color.YELLOW;
			else if (JOURNAL_NAME_ANNOTATION_TYPE.equals(type))
				color = Color.CYAN;
			else if (SERIES_IN_JOURNAL_ANNOTATION_TYPE.equals(type))
				color = FeedbackPanel.darken(Color.CYAN);
			else if (PUBLISHER_ANNOTATION_TYPE.equals(type))
				color = Color.YELLOW;
			else if (LOCATION_ANNOTATION_TYPE.equals(type))
				color = FeedbackPanel.darken(Color.YELLOW);
			else if (PART_DESIGNATOR_ANNOTATION_TYPE.equals(type))
				color = Color.PINK;
			else if (NEXT_REFERENCE_ANNOTATION_TYPE.equals(type))
				color = Color.GRAY;
			else if (VOLUME_REFERENCE_ANNOTATION_TYPE.equals(type))
				color = Color.BLUE;
			else if (PAGINATION_ANNOTATION_TYPE.equals(type) || PAGE_NUMBER_TYPE.equals(type) || PAGE_RANGE_ANNOTATION_TYPE.equals(type))
				color = Color.MAGENTA;
			else if (PUBLICATION_DOI_ANNOTATION_TYPE.equals(type))
				color = Color.LIGHT_GRAY;
			else if (PUBLICATION_URL_ANNOTATION_TYPE.equals(type))
				color = Color.LIGHT_GRAY;
			else if (BOOK_CONTENT_INFO_ANNOTATION_TYPE.equals(type))
				color = FeedbackPanel.brighten(Color.BLUE);
			else if (ACCESS_DATE_ANNOTATION_TYPE.equals(type))
				color = Color.GRAY;
			else color = new Color(Color.HSBtoRGB(((float) Math.random()), 0.5f, 1.0f));
			this.highlightAttributeCache.put(type, color);
		}
		return color;
	}
	
	private String authorRepetitionMarkerRegEx = 
			"(" +
				"([\\-]+)" +
				"|" +
				"(Ders(\\.|elbe))" +
				"|" +
				"(Dies(\\.|(elben?)))" +
				"|" +
				"(Same(\\sas\\sabove)?)" +
			")";
	
	private String editorListLabelBaseRegEx = 
			"(" +
				"(Ed(s|s\\.|\\.|itors|itor)?)" +
				"|" +
				"(Red(s|s\\.|\\.|acteurs|acteur)?)" +
				"|" +
				"(Hrsg\\.|Hg\\.)" +
			")";
	private String editorListLabelRegEx = 
			"(" +
				"(\\(" + this.editorListLabelBaseRegEx + "\\))" +
				"|" +
				"(\\[" + this.editorListLabelBaseRegEx + "\\])" +
				"|" +
				"(" + this.editorListLabelBaseRegEx + ")" +
			")";
	
//	private String authorLastNameBaseRegEx = 
//			"([A-Za-z]+\\'?)?" +
//			"(" +
//				"(" +
//					"[A-Z]" +
//					"(" +
//						"([a-z\\-]*[aeiouy][a-z]*)" +
//						"|" +
////						"([A-Z]*[AEIOUY][A-Z]*)" +
////						"|" +
//						"([a-z]{1,2})" +
//					")" +
//				")" +
//				"|" +
//				"(" +
//					"[AEIOUY]" +
////					"(" +
//						"([a-z\\-]*[a-z]+)" +
////						"|" +
////						"[A-Z]+" +
////					")" +
//				")" +
//			")" +
//			"(\\'[a-z]+)?" +
//			"";
//	private String authorLastNameRegEx = "(" + this.authorLastNameBaseRegEx + ")((\\-|\\s)?" + this.authorLastNameBaseRegEx + ")*";
//	
//	private String authorLastNameAllCapsBaseRegEx = 
//			"([A-Za-z]+\\'?)?" +
//			"(" +
////				"(" +
////					"[A-Z]" +
////					"(" +
////						"([a-z\\-]*[aeiouy][a-z]*)" +
////						"|" +
//						"([A-Z]*[AEIOUY][A-Z]*)" +
////						"|" +
////						"([a-z]{1,2})" +
////					")" +
////				")" +
//				"|" +
//				"(" +
//					"[AEIOUY]" +
////					"(" +
////						"([a-z\\-]*[a-z]+)" +
////						"|" +
//						"[A-Z]+" +
////					")" +
//				")" +
//			")" +
////			"(\\'[a-z]+)?" +
//			"";
//	private String authorLastNameAllCapsRegEx = "(" + this.authorLastNameAllCapsBaseRegEx + ")((\\-|\\s)?" + this.authorLastNameAllCapsBaseRegEx + ")*";
//	
//	private String authorFirstNameBaseRegEx = 
//			"(" +
//				"[A-Z]" +
//				"(" +
//					"([a-z\\-]*[aeiouy][a-z]*)" +
//					"|" +
//					"([A-Z]*[AEIOUY][A-Z]*)" +
//				")" +
//			")" +
//			"|" +
//			"(" +
//				"[AEIOUY]" +
//				"(" +
//					"[a-z\\-]+" +
//					"|" +
//					"[A-Z]+" +
//				")" +
//			")";
//	private String authorFirstNameRegEx = "(" + this.authorFirstNameBaseRegEx + ")((\\-|\\s)?" + this.authorFirstNameBaseRegEx + ")*";
//	
//	private String authorFirstNameAllCapsBaseRegEx = 
//			"(" +
//				"[A-Z]" +
//				"(" +
//					"([a-z\\-]*[aeiouy][a-z]*)" +
//					"|" +
//					"([A-Z]*[AEIOUY][A-Z]*)" +
//				")" +
//			")" +
//			"|" +
//			"(" +
//				"[AEIOUY]" +
//				"(" +
//					"[a-z\\-]+" +
//					"|" +
//					"[A-Z]+" +
//				")" +
//			")";
//	private String authorFirstNameAllCapsRegEx = "(" + this.authorFirstNameAllCapsBaseRegEx + ")((\\-|\\s)?" + this.authorFirstNameAllCapsBaseRegEx + ")*";
//	
//	private String authorInitialsBaseRegEx = 
//		"[A-Z]" +
//		"(" +
//			"[a-z]?" +
//			"\\." +
//		")?";
//	private String authorInitialsRegEx = "(" + this.authorInitialsBaseRegEx + ")(((\\s?\\-\\s?)|\\s)?" + this.authorInitialsBaseRegEx + ")*";
//	
//	private String authorNameAffixRegEx = 
//		"(" +
//			"\\,?\\s*" +
//			"(" +
//				"Jr" +
//				"|" +
//				"Sr" +
//				"|" +
//				"(" +
//					"X{0,3}" +
//					"(" +
//						"I{1,4}" +
//						"|" +
//						"IV" +
//						"|" +
//						"(VI{0,4})" +
//						"|" +
//						"IX" +
//					")" +
//				")" +
//				"|" +
//				"(1\\s?st)" +
//				"|" +
//				"(2\\s?nd)" +
//				"|" +
//				"(3\\s?rd)" +
//				"|" +
//				"([4-9]\\s?th)" +
//			")" +
//			"\\.?" +
//		")";
	
	private String nobleTitleNameRegEx = "([A-Z][a-z]{3,}\\s)+(of|the|(of\\sthe)|de|(de\\sla)|von|van|(von\\sder)|(van\\sder)|vom|(von\\sden)|(von\\sdem)|(van\\sde))+(\\s[A-Z][a-z]{3,})+";
	
	private StringVector nobleTitleStarts = new StringVector();
	private StringVector authorNameStopWords = new StringVector();
	private StringVector authorListSeparators = new StringVector();
	
	private StringVector knownAuthorLastNames = new StringVector();
	private StringVector knownAuthorNames = new StringVector();
	
	private TokenBagDictionary knownAuthors = new TokenBagDictionary();
	private StringVector knownNonAuthorNames = new StringVector();
	private StringVector knownNonAuthorNameStarts = new StringVector();
	
	
	private String yearRegEx = "((1[5-9])|20)[0-9]{2}";//"[12][0-9]{3}";
	
	
	private String pageRegEx = 
			"(" +
				"(p\\.|page)" +
				"\\s" +
			")?" +
			"[1-9][0-9]{0,5}";
	private String ePageRegEx = "e\\s?[0-9]{1,7}";
	
	private String pageRangeArabicRegEx = 
			"(" +
				"(pp\\.|pages)" +
				"\\s" +
			")?" +
			"[1-9][0-9]{0,5}\\s*[\\-\\u2012-\\u2015]\\s*[1-9][0-9]{0,5}";
	private String romanNumberRegEx = "((c?m+)?(c?d)?(x?c+)?(x?l)?(i?x+)?(i?v)?(i+)?)";
	private String pageRangeRomanRegEx = 
			"(" +
				"(pp\\.|pages)" +
				"\\s" +
			")?" +
			this.romanNumberRegEx +
			"\\s*[\\-\\u2012-\\u2015]\\s*" +
			this.romanNumberRegEx;
	
	
	private String partDesignatorRegEx = "(([1-9][0-9]*+)|([Ii]?[Xx]*[Vv]?[Ii]*)|([A-Z]))";
	
	private StringVector numberingInvalidatorsLeading = new StringVector();
	private StringVector numberingInvalidatorsTailing = new StringVector();
	private StringVector bookContentInfoNumberingInvalidatorsTailing = new StringVector();
	private StringVector titleNumberPatterns = new StringVector();
	
	private StringVector volumeDesignatorHints = new StringVector();
	private StringVector issueDesignatorHints = new StringVector();
	private StringVector numberDesignatorHints = new StringVector();
	private StringVector fascicleDesignatorHints = new StringVector();
	private StringVector seriesDesignatorHints = new StringVector();
	private StringVector partDesignatorHints = new StringVector();
	
	private StringVector partDesignatorBlockSeparators = new StringVector();
	
	private StringVector dateMonths = aggregateDictionaries(DateTimeUtils.getMonthDictionaries());
	private StringVector dateDays = aggregateDictionaries(DateTimeUtils.getDayDictionaries());
	private StringVector dateLabels = new StringVector();
	private static StringVector aggregateDictionaries(StringVector[] dicts) {
		StringVector dict = new StringVector();
		for (int d = 0; d < dicts.length; d++)
			dict.addContent(dicts[d]);
		return dict;
	}
	
	private String titleCaseAbbreviationRegEx = 
		"(" +
			"(" +
				"[A-Z]" +
				"[a-z]*" +
				"(\\.?\\-)" +
			")*" +
			"(" +
				"[A-Z]" +
				"(" +
					"[a-z]*" +
					"[a-df-z]" + // abbreviations almost never end with an 'e'
				")?" +
				"\\." +
			")" +
			"(" +
				"\\-" +
				"[A-Za-z]" +
				"[a-z]*" +
				"\\." +
			")*" +
		")" +
		"|" +
		"([1-9][0-9]*)";
	private String titleCaseAbbreviationBlockRegEx = ("" +
			"(" + this.titleCaseAbbreviationRegEx + ")" +
			"(" +
				"\\s*" +
				"([a-z]{1,4}\\.?\\s)*" +
				"(" + this.titleCaseAbbreviationRegEx + ")" +
			")+" +
			"");
	
	private String titleCaseTokenRegEx = 
			"(" +
				"(" +
					"((d|l)\\')?" +
					"[A-Z]" +
					"(" +
						"([a-z]{0,3}\\.\\s\\-\\s)" +
						"|" + // catch Gamta's normalization (will add spaces around dash if preceeded by dot)
						"(([A-Z]+|[a-z]+)?\\-)" +
					")" +
				")*" +
				"(" +
					"((d|l)\\')?" +
					"[A-Z]" +
					"(" +
						"[A-Z]+" +
						"|" +
						"([a-z]{0,3}\\.)" +
						"|" +
						"[a-z]+" +
					")" +
				")" +
			")" +
			"|" +
			"([1-9][0-9]*)" +
			"";
	
	private StringVector titleCaseBlockStopWords = Gamta.getNoiseWords();
	private StringVector knownTitleCaseBlockPatterns = new StringVector();
	private StringVector countryNames = new StringVector();
	private StringVector conferenceSynonyms = new StringVector();
	private StringVector titleCaseAbbreviations = new StringVector();
	
	private StringVector wordBlockExcluded = new StringVector();
	private StringVector wordBlockExcludePatterns = new StringVector();
	
	private TokenBagDictionary knownJournalsAndPublishers = new TokenBagDictionary(true);
	private StringVector journalPublisherStopWords = new StringVector();
	private StringVector journalPublisherExcluded = new StringVector();
	private WordUseStat jopWordStat = new WordUseStat();
	
	private static final String urlHostChar = "[a-zA-Z0-9\\-]";
	private static final String urlPathChar = "[a-zA-Z0-9\\.\\-\\_\\~\\!\\$\\&\\'\\(\\)\\[\\]\\{\\}\\*\\+\\,\\;\\=\\:\\@]";
	private static final String urlPattern = 
			"(https|http|ftp)\\:\\/\\/" + // protocol
			"" + urlHostChar + "+(\\." + urlHostChar + "+)+" + // host
			"(\\:[0-9]++)?" + // port (optional)
			"(\\/" + urlPathChar + "+(\\." + urlPathChar + "+)*)*" + // path (optional)
			"[\\/?\\p{Graph}]*" + // arbitrary character last path step (also matches path terminating slash)
			"(\\?[\\p{Graph}]*)?"; // query
	private static final String urlStartPattern = "(https|http|ftp)\\:\\/\\/[\\p{Graph}]*"; // protocol followed by any non-space character
	private static final String urlFragmentPattern = "[\\p{Graph}]++";
	private static final String doiPattern =
				"(" +
					"(https|http)\\:\\/\\/(dx\\.)?doi\\.org\\/" +
					"|" +
					"(doi\\:\\s?)" +
				")?" +
				"10\\.[0-9]++\\/[\\p{Graph}]++";
	private StringVector urlAvailableFromLabels = new StringVector();
	
	private StringVector relevantTypes = new StringVector();
	private StringVector transferableTypes = new StringVector();
	
	private TreeMap referenceTypes = new TreeMap();
	
	private BibRefTypeSystem referenceTypeSystem = null;
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.gamta.util.AbstractConfigurableAnalyzer#initAnalyzer()
	 */
	public void initAnalyzer() {
		
		//	read stop words for title case blocks
		this.titleCaseBlockStopWords.clear();
		this.titleCaseBlockStopWords.addContentIgnoreDuplicates(this.readList("titleCaseBlockStopWords"));
		
		//	read journal/publisher tokens
		this.jopWordStat = new WordUseStat();
		try {
			BufferedReader jwsBr = new BufferedReader(new InputStreamReader(this.dataProvider.getInputStream("knownJopWords.txt"), "UTF-8"));
			this.jopWordStat.readData(jwsBr);
			jwsBr.close();
		} catch (IOException fnfe) {}
		
		//	read stop words for author names
		this.authorNameStopWords.clear();
		this.authorNameStopWords.addContentIgnoreDuplicates(this.readList("authorNameStopWords"));
		
		//	read author list separators
		this.authorListSeparators.clear();
		this.authorListSeparators.addContentIgnoreDuplicates(this.readList("authorListSeparators"));
		
		//	read known author name list
		this.knownAuthorNames.clear();
		this.knownAuthorNames.addContentIgnoreDuplicates(this.readList("knownAuthorNames"));
		
		//	read known author last name list
		this.knownAuthorLastNames.clear();
		this.knownAuthorLastNames.addContentIgnoreDuplicates(this.readList("knownAuthorLastNames"));
		
		//	read base regular expression patterns and assemble main patterns
		this.nobleTitleNameRegEx = this.readRegEx("nobleTitleName", this.nobleTitleNameRegEx);
		this.nobleTitleStarts.addContentIgnoreDuplicates(this.readList("nobleTitleStarts"));
		
		this.authorRepetitionMarkerRegEx = this.readRegEx("authorRepetitionMarker", this.authorRepetitionMarkerRegEx);
		
		this.editorListLabelBaseRegEx = this.readRegEx("editorListLabelBase", this.editorListLabelBaseRegEx);
		this.editorListLabelRegEx = 
				"(" +
					"(\\(" + this.editorListLabelBaseRegEx + "\\))" +
					"|" +
					"(\\[" + this.editorListLabelBaseRegEx + "\\])" +
					"|" +
					"(\\,?" + this.editorListLabelBaseRegEx + ")" +
				")";
		
		this.knownNonAuthorNames.addContentIgnoreDuplicates(this.readList("knownNonAuthorNames"));
		this.knownNonAuthorNameStarts.addContentIgnoreDuplicates(this.readList("knownNonAuthorNameStarts"));
		
		
		this.pageRegEx = this.readRegEx("page", this.pageRegEx);
		this.pageRangeArabicRegEx = this.readRegEx("pageRangeArabic", this.pageRangeArabicRegEx);
		this.pageRangeRomanRegEx = this.readRegEx("pageRangeRoman", this.pageRangeRomanRegEx);
		
		this.numberingInvalidatorsLeading.clear();
		this.numberingInvalidatorsLeading.addContentIgnoreDuplicates(this.readList("numberingInvalidatorsLeading"));
		
		this.numberingInvalidatorsTailing.clear();
		this.numberingInvalidatorsTailing.addContentIgnoreDuplicates(this.readList("numberingInvalidatorsTailing"));
		
		this.bookContentInfoNumberingInvalidatorsTailing.clear();
		this.bookContentInfoNumberingInvalidatorsTailing.addContentIgnoreDuplicates(this.readList("bookContentInfoNumberingInvalidatorsTailing"));
		
		this.numberingInvalidatorsTailing.addContentIgnoreDuplicates(this.bookContentInfoNumberingInvalidatorsTailing);
		
		this.titleNumberPatterns.clear();
		this.titleNumberPatterns.addContentIgnoreDuplicates(this.readList("titleNumberPatterns"));
		
		this.partDesignatorRegEx = this.readRegEx("partDesignator", this.partDesignatorRegEx);
		
		this.volumeDesignatorHints.parseAndAddElements("v.;vol.;volume;Band;Bd.;Heft", ";");
		this.issueDesignatorHints.parseAndAddElements("i.;issue", ";");
		this.numberDesignatorHints.parseAndAddElements("n.;nr;nr.;no;no.;number", ";");
		this.fascicleDesignatorHints.parseAndAddElements("f.;fasc.;fascicle", ";");
		this.seriesDesignatorHints.parseAndAddElements("s.;ser.;series", ";");
		this.seriesDesignatorHints.parseAndAddElements("sect.;section", ";");
		
		this.partDesignatorHints.addContentIgnoreDuplicates(this.volumeDesignatorHints);
		this.partDesignatorHints.addContentIgnoreDuplicates(this.issueDesignatorHints);
		this.partDesignatorHints.addContentIgnoreDuplicates(this.numberDesignatorHints);
		this.partDesignatorHints.addContentIgnoreDuplicates(this.fascicleDesignatorHints);
		this.partDesignatorHints.addContentIgnoreDuplicates(this.seriesDesignatorHints);
		
		this.partDesignatorBlockSeparators.parseAndAddElements("(;);,;/;-", ";");
		
		this.dateLabels.clear();
		this.dateLabels.addContentIgnoreDuplicates(this.readList("dateLabels"));
		this.urlAvailableFromLabels.clear();
		this.urlAvailableFromLabels.addContentIgnoreDuplicates(this.readList("urlAvailableFromLabels"));
		
		
		this.titleCaseAbbreviationRegEx = this.readRegEx("titleCaseAbbreviation", this.titleCaseAbbreviationRegEx);
		this.titleCaseAbbreviationBlockRegEx = ("" +
				"(" + this.titleCaseAbbreviationRegEx + ")" +
				"(" +
					"\\s*" +
					"([a-z]{1,4}\\.?\\s)*" +
					"(" + this.titleCaseAbbreviationRegEx + ")" +
				")+" +
				"");
		
		this.titleCaseTokenRegEx = this.readRegEx("titleCaseToken", this.titleCaseTokenRegEx);
		
		//	read title case abbreviations and countries
		this.titleCaseAbbreviations.clear();
		this.titleCaseAbbreviations.addContentIgnoreDuplicates(this.readList("titleCaseAbbreviations"));
		this.countryNames.clear();
		this.countryNames.addContentIgnoreDuplicates(this.readList("countries"));
		this.conferenceSynonyms.clear();
		this.conferenceSynonyms.addContentIgnoreDuplicates(this.readList("conferenceSynonyms"));
		this.wordBlockExcluded.clear();
		this.wordBlockExcluded.addContentIgnoreDuplicates(this.readList("wordBlockExcluded"));
		this.wordBlockExcludePatterns.clear();
		this.wordBlockExcludePatterns.addContentIgnoreDuplicates(this.readList("wordBlockExcludePatterns"));
		
		this.knownTitleCaseBlockPatterns.clear();
		this.knownTitleCaseBlockPatterns.addContentIgnoreDuplicates(this.readList("knownTitleCaseBlockPatterns"));
		for (int c = 0; c < this.conferenceSynonyms.size(); c++) {
			String cs = this.conferenceSynonyms.get(c);
			if (cs.endsWith("."))
				this.titleCaseAbbreviations.addElementIgnoreDuplicates(cs);
			this.knownTitleCaseBlockPatterns.addElement("Proceedings.*" + RegExUtils.escapeForRegEx(cs));
			this.knownTitleCaseBlockPatterns.addElement("Proc\\..*" + RegExUtils.escapeForRegEx(cs));
		}
		
		//	read data types & colors
		try {
			InputStream is = this.dataProvider.getInputStream("relevantTypes.txt");
			StringVector typeLines = StringVector.loadList(is);
			is.close();
			
			this.relevantTypes.clear();
			
			for (int t = 0; t < typeLines.size(); t++) {
				String typeLine = typeLines.get(t).trim();
				if ((typeLine.length() != 0) && !typeLine.startsWith("//")) {
					int split = typeLine.indexOf(' ');
					if (split == -1)
						this.relevantTypes.addElement(typeLine);
					else {
						String type = typeLine.substring(0, split).trim();
						Color color = FeedbackPanel.getColor(typeLine.substring(split).trim());
						this.relevantTypes.addElement(type);
						this.highlightAttributeCache.put(type, color);
					}
				}
			}
		} catch (IOException fnfe) {}
		
		//	add fix types
		this.relevantTypes.addElementIgnoreDuplicates(AUTHOR_ANNOTATION_TYPE);
		if (integrateVolumeRefs)
			this.relevantTypes.addElementIgnoreDuplicates(EDITOR_ANNOTATION_TYPE);
		this.relevantTypes.addElementIgnoreDuplicates(YEAR_ANNOTATION_TYPE);
		this.relevantTypes.addElementIgnoreDuplicates(TITLE_ANNOTATION_TYPE);
		if (detailOrigin) {
			this.relevantTypes.addElementIgnoreDuplicates(VOLUME_TITLE_ANNOTATION_TYPE);
			this.relevantTypes.addElementIgnoreDuplicates(JOURNAL_NAME_ANNOTATION_TYPE);
			this.relevantTypes.addElementIgnoreDuplicates(SERIES_IN_JOURNAL_ANNOTATION_TYPE);
			this.relevantTypes.addElementIgnoreDuplicates(PUBLISHER_ANNOTATION_TYPE);
			this.relevantTypes.addElementIgnoreDuplicates(LOCATION_ANNOTATION_TYPE);
			this.relevantTypes.removeAll(JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE);
		}
		else {
			this.relevantTypes.removeAll(VOLUME_TITLE_ANNOTATION_TYPE);
			this.relevantTypes.removeAll(JOURNAL_NAME_ANNOTATION_TYPE);
			this.relevantTypes.removeAll(SERIES_IN_JOURNAL_ANNOTATION_TYPE);
			this.relevantTypes.removeAll(PUBLISHER_ANNOTATION_TYPE);
			this.relevantTypes.removeAll(LOCATION_ANNOTATION_TYPE);
			this.relevantTypes.addElementIgnoreDuplicates(JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE);
		}
		if (integrateVolumeRefs)
			this.relevantTypes.addElementIgnoreDuplicates(VOLUME_TITLE_ANNOTATION_TYPE);
		this.relevantTypes.addElementIgnoreDuplicates(PAGINATION_ANNOTATION_TYPE);
		this.relevantTypes.addElementIgnoreDuplicates(PART_DESIGNATOR_ANNOTATION_TYPE);
		this.relevantTypes.addElementIgnoreDuplicates(PUBLICATION_DOI_ANNOTATION_TYPE);
		this.relevantTypes.addElementIgnoreDuplicates(PUBLICATION_URL_ANNOTATION_TYPE);
		this.relevantTypes.addElementIgnoreDuplicates(BOOK_CONTENT_INFO_ANNOTATION_TYPE);
		this.relevantTypes.addElementIgnoreDuplicates(ACCESS_DATE_ANNOTATION_TYPE);
		
		//	add transferable types TODO check out if transfer is sensible (causes errors if element not given in subsequent references)
		this.transferableTypes.addElementIgnoreDuplicates(AUTHOR_ANNOTATION_TYPE);
		this.transferableTypes.addElementIgnoreDuplicates(YEAR_ANNOTATION_TYPE);
		
		//	add available reference types TODO load descriptors of reference types from BibRefTypeSystem
		this.referenceTypes.clear();
		this.referenceTypes.put(JOURNAL_ARTICEL_REFERENCE_TYPE, new BibRefType(JOURNAL_ARTICEL_REFERENCE_TYPE, "Journal Article"));
		this.referenceTypes.put(JOURNAL_VOLUME_REFERENCE_TYPE, new BibRefType(JOURNAL_VOLUME_REFERENCE_TYPE, "Journal Volume"));
		this.referenceTypes.put(BOOK_REFERENCE_TYPE, new BibRefType(BOOK_REFERENCE_TYPE, "Book / Thesis / Monograph"));
		this.referenceTypes.put(BOOK_CHAPTER_REFERENCE_TYPE, new BibRefType(BOOK_CHAPTER_REFERENCE_TYPE, "Book Chapter"));
		this.referenceTypes.put(PROCEEDINGS_REFERENCE_TYPE, new BibRefType(PROCEEDINGS_REFERENCE_TYPE, "Conference Proceedings"));
		this.referenceTypes.put(PROCEEDINGS_PAPER_REFERENCE_TYPE, new BibRefType(PROCEEDINGS_PAPER_REFERENCE_TYPE, "Proceedings Paper"));
		this.referenceTypes.put(URL_REFERENCE_TYPE, new BibRefType(URL_REFERENCE_TYPE, "Online Document / Website / etc."));
		
		this.referenceTypeSystem = BibRefTypeSystem.getInstance(this.dataProvider, "RefClassifierTypeSystem.xml", false);
		
		//	load learned authors
		try {
			InputStream is = this.dataProvider.getInputStream("knownAuthors.txt");
			StringVector knownAuthors = StringVector.loadList(new InputStreamReader(is, "UTF-8"));
			is.close();
			
			this.knownAuthors = new TokenBagDictionary();
			
			for (int a = 0; a < knownAuthors.size(); a++)
				this.knownAuthors.addEntry(knownAuthors.get(a));
		}
		catch (IOException fnfe) {
			fnfe.printStackTrace(System.out);
		}
		
		//	load learned journal names and publishers
		try {
			InputStream is = this.dataProvider.getInputStream("knownJournalsAndPublishers.txt");
			StringVector knownJournalsAndPublishers = StringVector.loadList(new InputStreamReader(is, "UTF-8"));
			is.close();
			
			this.knownJournalsAndPublishers = new TokenBagDictionary(true);
			
			for (int a = 0; a < knownJournalsAndPublishers.size(); a++)
				this.knownJournalsAndPublishers.addEntry(knownJournalsAndPublishers.get(a));
		}
		catch (IOException fnfe) {
			fnfe.printStackTrace(System.out);
		}
		
		//	stop words for recognition
		this.journalPublisherStopWords.clear();
		this.journalPublisherStopWords.addContentIgnoreDuplicates(this.readList("journalPublisherStopWords"));
		this.journalPublisherExcluded.clear();
		this.journalPublisherExcluded.addContentIgnoreDuplicates(this.readList("journalPublisherExcluded"));
		
		//	register descriptions for style parameters ...
		ParameterGroupDescription pgd;
		
		//	... for author lists ...
		pgd = new ParameterGroupDescription(BIBLIOGRAPHIC_REFERENCE_TYPE + "." + AUTHOR_ANNOTATION_TYPE);
		if (DocumentStyle.getParameterGroupDescription(pgd.parameterNamePrefix) == null) {
			pgd.setLabel("Author Names in Bibliographic References");
			pgd.setDescription("Parameters detailing on the representation of author (and editor) names in the bibliography of a document.");
			pgd.setParamLabel("nameListSeparatorPattern", "Author List Separator Pattern");
			pgd.setParamDescription("nameListSeparatorPattern", "A pattern matching the punctuation mark and/or word(s) used throughout author lists to separate any author names.");
			pgd.setParamLabel("nameListEndSeparatorPattern", "Author List End Separator Pattern");
			pgd.setParamDescription("nameListEndSeparatorPattern", "A pattern matching the punctuation mark and/or word(s) separating the very last two author names in a list; defaults to general separator pattern if absent.");
			ProperNameUtils.addParameterDescriptions(pgd);
			DocumentStyle.addParameterGroupDescription(pgd);
		}
		
		//	... as well as any other parameters in use
		pgd = new ParameterGroupDescription(BIBLIOGRAPHIC_REFERENCE_TYPE);
		if (DocumentStyle.getParameterGroupDescription(pgd.parameterNamePrefix) == null) {
			pgd.setLabel("Bibliographic References in General");
			pgd.setDescription("Parameters describing the layout and styling of individual references in the bibliography of a document.");
			pgd.setParamLabel("numberingPattern", "Reference Numbering Pattern");
			pgd.setParamDescription("numberingPattern", "A pattern matching the numbering of references; only applicable if such a reference style is in use in documents described by a given style, set to 'NONE' to explicitly indicate non-numbered references.");
			DocumentStyle.addParameterGroupDescription(pgd);
		}
	}
	
	private String[] readList(String name) {
		StringVector list = new StringVector();
		try {
			BufferedReader br = new BufferedReader(new InputStreamReader(this.dataProvider.getInputStream(name + ".list.txt"), "UTF-8"));
			for (String listEntry; (listEntry = br.readLine()) != null;) {
				if ((listEntry.length() != 0) && !listEntry.startsWith("//"))
					list.addElement(listEntry);
			}
			br.close();
		}
		catch (IOException ioe) {
			System.out.println("Exception loading list '" + name + "': " + ioe.getMessage());
		}
		return list.toStringArray();
	}
	
	private String readRegEx(String name, String def) {
		try {
			InputStream is = this.dataProvider.getInputStream(name + ".regEx.txt");
			StringVector regEx = StringVector.loadList(new InputStreamReader(is, "UTF-8"));
			is.close();
			return RegExUtils.normalizeRegEx(regEx.concatStrings("\n"));
		}
		catch (IOException ioe) {
			System.out.println("Exception loading pattern '" + name + "': " + ioe.getMessage());
			return def;
		}
	}
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.gamta.util.AbstractConfigurableAnalyzer#exitAnalyzer()
	 */
	public void exitAnalyzer() {
		
		//	store learned authors
		if (this.dataProvider.isDataEditable("knownAuthors.txt")) try {
			StringVector knownAuthors = new StringVector();
			for (StringIterator sit = this.knownAuthors.getStringEntryIterator(); sit.hasMoreStrings();)
				knownAuthors.addElementIgnoreDuplicates(sit.nextString());
			knownAuthors.sortLexicographically();
			
			OutputStream os = this.dataProvider.getOutputStream("knownAuthors.txt");
			knownAuthors.storeContent(new OutputStreamWriter(os, "UTF-8"));
			os.flush();
			os.close();
		} catch (IOException fnfe) {}
		
		//	store learned journal names and publishers
		if (this.dataProvider.isDataEditable("knownJournalsAndPublishers.txt")) try {
			StringVector knownJournalsAndPublishers = new StringVector();
			for (StringIterator sit = this.knownJournalsAndPublishers.getStringEntryIterator(); sit.hasMoreStrings();)
				knownJournalsAndPublishers.addElementIgnoreDuplicates(sit.nextString());
			knownJournalsAndPublishers.sortLexicographically();
			
			OutputStream os = this.dataProvider.getOutputStream("knownJournalsAndPublishers.txt");
			knownJournalsAndPublishers.storeContent(new OutputStreamWriter(os, "UTF-8"));
			os.flush();
			os.close();
		} catch (IOException fnfe) {}
		
		//	store learned journal/publisher tokens
		if (this.dataProvider.isDataEditable("knownJopWords.txt") && this.jopWordStat.isDirty()) try {
			BufferedWriter jwsBw = new BufferedWriter(new OutputStreamWriter(this.dataProvider.getOutputStream("knownJopWords.txt"), "UTF-8"));
			this.jopWordStat.writeData(jwsBw);
			jwsBw.close();
		} catch (IOException fnfe) {}
	}
	
	//	TODO use Analyzer Config API for regular expression patterns, with fixed names, forbidding to delete any of the built-in patterns
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.gamta.util.AbstractConfigurableAnalyzer#getConfigTitle()
	 */
	protected String getConfigTitle() {
		return "Configure RefParse";
	}
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.gamta.util.AbstractConfigurableAnalyzer#customizeConfigDialog(javax.swing.JDialog)
	 */
	protected void customizeConfigDialog(JDialog dialog) {
		//	TODO use analyzer config API
		super.customizeConfigDialog(dialog);
	}
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.gamta.util.AbstractConfigurableAnalyzer#getConfigPanels(javax.swing.JDialog)
	 */
	protected AnalyzerConfigPanel[] getConfigPanels(JDialog dialog) {
		//	TODO use analyzer config API
		return super.getConfigPanels(dialog);
	}
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.gamta.util.AbstractConfigurableAnalyzer#configureProcessor()
	 */
	public void configureProcessor() {
		
		//	store current data so it appears in config dialogs
		this.exitAnalyzer();
		
		//	configure processor
		super.configureProcessor();
		
		//	put changes in effect
		this.initAnalyzer();
	}

	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.gamta.util.Analyzer#process(de.uka.ipd.idaho.gamta.MutableAnnotation, java.util.Properties)
	 */
	public void process(MutableAnnotation data, Properties parameters) {}
	
	AuthorListStyle parseBibRefs(MutableAnnotation data, MutableAnnotation[] bibRefAnnots, Properties parameters, AuthorListStyle authorListStyle, ProgressMonitor pm) {
		
		//	check arguments
		if (bibRefAnnots.length == 0)
			return authorListStyle;
		
		//	filter out leading reference numbers
		int[] refNums = new int[bibRefAnnots.length];
		int refNumIndex = -1;
		int refStartIndex = 0;
		MutableAnnotation[] fullBibRefAnnots = null;
		for (int n = 0; n < 2; n++) {
			Arrays.fill(refNums, -1);
			boolean allRefNums = true;
			for (int r = 0; r < bibRefAnnots.length; r++) {
				if (bibRefAnnots[r].size() <= n) {
					allRefNums = false;
					break;
				}
				if (bibRefAnnots[r].valueAt(n).matches("[1-9][0-9]*"))
					refNums[r] = Integer.parseInt(bibRefAnnots[r].valueAt(n));
				else {
					allRefNums = false;
					break;
				}
			}
			if (!allRefNums)
				continue;
			for (int r = 1; r < bibRefAnnots.length; r++)
				if (refNums[r-1] != (refNums[r]-1)) {
					allRefNums = false;
					break;
				}
			if (!allRefNums)
				continue;
			refNumIndex = n;
		}
		
		//	found reference numbers, also get rid of associated punctuation
		if (refNumIndex != -1) {
			refStartIndex = refNumIndex+1;
			while ((refStartIndex < bibRefAnnots[0].size()) && Gamta.isPunctuation(bibRefAnnots[0].valueAt(refStartIndex))) {
				boolean punctuationMatch = true;
				for (int r = 1; r < bibRefAnnots.length; r++) {
					if (bibRefAnnots[r].size() <= refStartIndex) {
						punctuationMatch = false;
						break;
					}
					if (!bibRefAnnots[r].valueAt(refStartIndex).equals(bibRefAnnots[0].valueAt(refStartIndex))) {
						punctuationMatch = false;
						break;
					}
				}
				if (punctuationMatch)
					refStartIndex++;
				else break;
			}
			fullBibRefAnnots = new MutableAnnotation[bibRefAnnots.length];
		}
		
		//	cut reference numbers
		if (refStartIndex != 0)
			for (int r = 0; r < bibRefAnnots.length; r++) {
				fullBibRefAnnots[r] = bibRefAnnots[r];
				bibRefAnnots[r] = bibRefAnnots[r].addAnnotation(fullBibRefAnnots[r].getType(), refStartIndex, (fullBibRefAnnots[r].size() - refStartIndex));
				bibRefAnnots[r].copyAttributes(fullBibRefAnnots[r]);
			}
		
		//	initialize data structures
		BibRef[] bibRefs = new BibRef[bibRefAnnots.length];
		
		//	initialize data containers
		for (int r = 0; r < bibRefAnnots.length; r++)
			bibRefs[r] = new BibRef(bibRefAnnots[r]);
		
		//	get document style if available
		DocumentStyle docStyle = DocumentStyle.getStyleFor(data);
		if (docStyle == null)
			docStyle = new DocumentStyle(new PropertiesData(new Properties()));
		DocumentStyle bibRefStyle = docStyle.getSubset(BIBLIOGRAPHIC_REFERENCE_TYPE);
		
		//	do parsing
		AuthorListStyle als = this.parseBibRefs(bibRefs, authorListStyle, bibRefStyle, pm);
		
		//	un-cut reference numbers
		if (refStartIndex != 0)
			for (int r = 0; r < bibRefAnnots.length; r++) {
				fullBibRefAnnots[r].copyAttributes(bibRefAnnots[r]);
				fullBibRefAnnots[r].removeAnnotation(bibRefAnnots[r]);
				bibRefAnnots[r] = fullBibRefAnnots[r];
			}
		
		//	finally ...
		return als;
	}
	
	AuthorListStyle parseBibRefs(BibRef[] bibRefs, AuthorListStyle authorListStyle, DocumentStyle bibRefStyle, ProgressMonitor pm) {
		long start;
		
		//	get and wrap author name style
		DocumentStyle authorNameStyle = bibRefStyle.getSubset(AUTHOR_ANNOTATION_TYPE);
		NameStyle nameStyle = NameStyle.createFromTemplate(authorNameStyle);
		
		//	initialize data containers and extract basic details (collect evidence on name form along the way)
		pm.setStep("Extracting basic details");
		pm.setBaseProgress(0);
		pm.setMaxProgress(35);
		start = System.currentTimeMillis();
		for (int r = 0; r < bibRefs.length; r++) {
			pm.setProgress((r * 100) / bibRefs.length);
			
			//	mark numbers in contexts like "VLDB-11", "VLDB '11", "of the 2011 Joint Conference", etc.
			this.markTitleNumbers(bibRefs[r]);
			
			//	mark base details if necessary
			this.getBaseDetails(bibRefs[r], nameStyle);
		}
		System.out.println("TIME: Base details extracted after " + (System.currentTimeMillis() - start) + "ms");
		
		/* TODO
Also secure blocks better, adding second, punctuation-aware signature:
==> better backing for actual "<volume>, <pageNumber>" instances
==> better filtering for phony ones
==> keep some fuzziness, though, as colon in "<volume> (<issue>): <pagination>" might be lacking occasionally (one instance in test set)
  ==> maybe simply be lenient about punctuation if number block covers three or more individual numbers

Observe in the long haul if any of these rules does more harm than good !!!
		 */
		
		//	make sure every reference has a year outside part designator and pagination blocks
		pm.setStep("Assessing basic details");
		pm.setBaseProgress(35);
		pm.setMaxProgress(37);
		start = System.currentTimeMillis();
		boolean filterByNumberDetailBlocks = true;
		for (int r = 0; r < bibRefs.length; r++) {
			pm.setProgress((r * 100) / bibRefs.length);
			if (bibRefs[r].preExistingStructure)
				continue;
			if (bibRefs[r].numberDetailBlock == null)
				continue;
			if (bibRefs[r].years.length == 0)
				continue;
			if (bibRefs[r].numberDetailBlock.hasAttribute("year"))
				continue;
			boolean allYearsInNumberDetailBlock = true;
			for (int y = 0; y < bibRefs[r].years.length; y++) {
				if (AnnotationUtils.liesIn(bibRefs[r].years[y], bibRefs[r].numberDetailBlock))
					continue;
				allYearsInNumberDetailBlock = false;
				break;
			}
			if (allYearsInNumberDetailBlock) {
				filterByNumberDetailBlocks = false;
				break;
			}
		}
		System.out.println("TIME: Base details assessed after " + (System.currentTimeMillis() - start) + "ms");
		
		//	run majority vote over number block semantics
		pm.setStep("Selecting number detail blocks");
		pm.setBaseProgress(37);
		pm.setMaxProgress(38);
		start = System.currentTimeMillis();
		this.assignNumberDetailBlocks(bibRefs);
		System.out.println("TIME: Number detail blocks assessed after " + (System.currentTimeMillis() - start) + "ms");
		
		//	filter years, part designators, and pagination based on blocks
		pm.setStep("Filtering number details");
		pm.setBaseProgress(38);
		pm.setMaxProgress(39);
		start = System.currentTimeMillis();
		for (int r = 0; r < bibRefs.length; r++) {
			pm.setProgress((r * 100) / bibRefs.length);
			if (bibRefs[r].preExistingStructure)
				continue;
			if (DEBUG) System.out.println("Filtering number details in " + bibRefs[r].annotation.toXML());
			if (filterByNumberDetailBlocks)
				this.filterBaseDetailNumbersByBlocks(bibRefs[r]);
			else this.filterBaseDetailNumbersByDashes(bibRefs[r]);
			this.filterBaseDetailNumbersByPageRanges(bibRefs[r]);
		}
		System.out.println("TIME: Base details filtered after " + (System.currentTimeMillis() - start) + "ms");
		
		//	classify part designators
		pm.setStep("Classifying part designators");
		pm.setBaseProgress(39);
		pm.setMaxProgress(40);
		start = System.currentTimeMillis();
		for (int r = 0; r < bibRefs.length; r++) {
			pm.setProgress((r * 100) / bibRefs.length);
			if (bibRefs[r].preExistingStructure)
				continue;
			this.classifyPartDesignators(bibRefs[r], true);
		}
		System.out.println("TIME: Base details classified after " + (System.currentTimeMillis() - start) + "ms");
		
		//	mark author lists
		pm.setStep("Getting author lists");
		pm.setBaseProgress(40);
		pm.setMaxProgress(45);
		start = System.currentTimeMillis();
		for (int r = 0; r < bibRefs.length; r++) {
			pm.setProgress((r * 100) / bibRefs.length);
			bibRefs[r].authorLists = this.getAuthorLists(bibRefs[r], bibRefs[r].annotation, bibRefs[r].authorNames, authorNameStyle);
		}
		System.out.println("TIME: Author lists extracted after " + (System.currentTimeMillis() - start) + "ms");
		
		//	filter author lists based on style
		pm.setStep("Filtering author lists");
		pm.setBaseProgress(45);
		pm.setMaxProgress(50);
		start = System.currentTimeMillis();
		if (authorListStyle == null)
			authorListStyle = this.getAuthorListStyle(bibRefs);
		this.filterAuthorLists(bibRefs, authorListStyle, nameStyle.getNameStopWords(), pm);
		System.out.println("TIME: Author lists filtered after " + (System.currentTimeMillis() - start) + "ms");
		
		//	extract all possible detail structures (as "<element> <punctuation>? <element> <punctuation>? <element> ...") and use the one which fits for most references
		pm.setStep("Collecting reference structures");
		pm.setBaseProgress(50);
		pm.setMaxProgress(55);
		start = System.currentTimeMillis();
		CountingSet structureCounts = new CountingSet();
		HashMap typeElementSets = new HashMap();
		HashMap summaryElementSets = new HashMap();
		HashMap punctSummaryElementSets = new HashMap();
		for (int r = 0; r < bibRefs.length; r++) {
			pm.setProgress((r * 100) / bibRefs.length);
			
			//	get structures
			this.getStructures(bibRefs[r]);
			
			//	index structures
			this.indexStructures(bibRefs[r], structureCounts, punctSummaryElementSets, punctSummaryElementSets, typeElementSets);
		}
		System.out.println("TIME: Structures generated after " + (System.currentTimeMillis() - start) + "ms");
		
		//	select best structure for each bibliographic reference, using global context
		pm.setStep("Selecting reference structures");
		pm.setBaseProgress(55);
		pm.setMaxProgress(60);
		start = System.currentTimeMillis();
		for (int r = 0; r < bibRefs.length; r++) {
			pm.setProgress((r * 100) / bibRefs.length);
			this.selectStructure(bibRefs[r], bibRefs.length, structureCounts, punctSummaryElementSets, summaryElementSets, typeElementSets);
		}
		System.out.println("TIME: Structures selected after " + (System.currentTimeMillis() - start) + "ms");
		
		//	fill in author list gaps (now that we have a structure established, we can work with more fault tolerance)
		pm.setStep("Filling in author list gaps");
		pm.setBaseProgress(60);
		pm.setMaxProgress(65);
		start = System.currentTimeMillis();
		int authorListLeading = 0;
		int authorListTerminated = 0;
		for (int r = 0; r < bibRefs.length; r++) {
			pm.setProgress((r * 100) / bibRefs.length);
			if (bibRefs[r].structure.punctSummaryString.matches("authorList\\s.*"))
				authorListLeading++;
			if (bibRefs[r].parentRef == null) {
				if (bibRefs[r].structure.punctSummaryString.matches("authorList\\s([\\.\\,\\:\\;\\(\\[]\\s)*year.*"))
					authorListTerminated++;
			}
			else {
				if (bibRefs[r].structure.punctSummaryString.matches("authorList\\s.*") && (bibRefs[r].editorListLabels.length != 0))
					authorListTerminated++;
			}
		}
		if (DEBUG) System.out.println("Author list is leading in " + authorListLeading + " references of " + bibRefs.length);
		if (DEBUG) System.out.println("Author list is terminated in " + authorListTerminated + " references of " + bibRefs.length);
		for (int r = 0; r < bibRefs.length; r++)
			this.completeAuthorLists(bibRefs[r], bibRefs.length, nameStyle, authorListStyle, ((authorListLeading * 3) > (bibRefs.length * 2)), ((authorListTerminated * 3) > (bibRefs.length * 2)));
		System.out.println("TIME: author lists completed after " + (System.currentTimeMillis() - start) + "ms");
		
		//	now that we're doing title, volume title, and journal/publisher together, we don't need to handle volume references any further
		if (bibRefs[0].parentRef != null)
			return authorListStyle;
		
		//	extract primary separator char
		pm.setStep("Determining primary detail separator");
		pm.setBaseProgress(65);
		pm.setMaxProgress(66);
		start = System.currentTimeMillis();
		String primarySeparator = this.selectPrimarySeparator(bibRefs);
		
		//	identify volume references
		pm.setStep("Extracting volume references");
		pm.setBaseProgress(66);
		pm.setMaxProgress(70);
		start = System.currentTimeMillis();
		for (int r = 0; r < bibRefs.length; r++) {
			pm.setProgress((r * 100) / bibRefs.length);
			if (bibRefs[r].preExistingStructure)
				continue;
			this.extractVolumeReference(bibRefs[r], primarySeparator, authorListStyle, nameStyle, authorNameStyle);
		}
		System.out.println("TIME: Volume references extracted after " + (System.currentTimeMillis() - start) + "ms");
		
		//	have to recurse even before getting title and origin, so to handle references whose origin lies outside an embedded volume reference
		if (integrateVolumeRefs) {
			pm.setStep("Parsing volume references");
			pm.setBaseProgress(70);
			pm.setMaxProgress(75);
			start = System.currentTimeMillis();
			this.processVolumeRefs(bibRefs, authorListStyle, bibRefStyle, new CascadingProgressMonitor(pm));
			System.out.println("TIME: Volume references processed after " + (System.currentTimeMillis() - start) + "ms");
		}
		
		//	get all unassigned word blocks
		pm.setStep("Collecting title and journal/publisher blocks");
		pm.setBaseProgress(75);
		pm.setMaxProgress(80);
		start = System.currentTimeMillis();
		for (int r = 0; r < bibRefs.length; r++) {
			pm.setProgress((r * 100) / bibRefs.length);
			this.getWordBlocks(bibRefs[r], bibRefs[r].structure.details);
			if (DEBUG) {
				System.out.println("Word blocks:");
				for (int b = 0; b < bibRefs[r].wordBlocks.length; b++)
					System.out.println(" - " + bibRefs[r].wordBlocks[b].getValue());
			}
		}
		System.out.println("TIME: Word blocks extracted after " + (System.currentTimeMillis() - start) + "ms");
		
		//	find most frequent after-title separator
		pm.setStep("Determining title terminator");
		pm.setBaseProgress(80);
		pm.setMaxProgress(81);
		start = System.currentTimeMillis();
		String tJopSeparator = this.selectTitleJournalPublisherSeparator(bibRefs);
		TokenSequence tJopSeparatorTokens = ((tJopSeparator.length() == 0) ? null : Gamta.newTokenSequence(tJopSeparator, bibRefs[0].annotation.getTokenizer()));
		System.out.println("TIME: T-JoP separator selected after " + (System.currentTimeMillis() - start) + "ms");
		
		//	classify word blocks as title, volume title, and journal/publisher
		pm.setStep("Selecting titles and journals/publishers");
		pm.setBaseProgress(81);
		pm.setMaxProgress(85);
		start = System.currentTimeMillis();
		for (int r = 0; r < bibRefs.length; r++) {
			pm.setProgress((r * 100) / bibRefs.length);
			if (bibRefs[r].preExistingStructure)
				continue;
			this.selectTitleJournalPublisher(bibRefs[r], tJopSeparator, tJopSeparatorTokens, bibRefs, false);
		}
		System.out.println("TIME: Title and JoP selected after " + (System.currentTimeMillis() - start) + "ms");
		
		//	filter paginations and part designators spanned by title or volume title
		pm.setStep("Position-filtering number details");
		pm.setBaseProgress(85);
		pm.setMaxProgress(88);
		start = System.currentTimeMillis();
		for (int r = 0; r < bibRefs.length; r++) {
			pm.setProgress((r * 100) / bibRefs.length);
			if (bibRefs[r].preExistingStructure)
				continue;
			this.filterBaseDetailNumbersByPosition(bibRefs[r]);
		}
		System.out.println("TIME: Part designators and paginations filered after " + (System.currentTimeMillis() - start) + "ms");
		
		//	clean up any remaining volume reference
		pm.setStep("Cleaning up volume references");
		pm.setBaseProgress(88);
		pm.setMaxProgress(90);
		start = System.currentTimeMillis();
		for (int r = 0; r < bibRefs.length; r++) {
			pm.setProgress((r * 100) / bibRefs.length);
			if (bibRefs[r].preExistingStructure)
				continue;
			if (bibRefs[r].volumeRef != null)
				AnnotationFilter.removeAnnotations(bibRefs[r].annotation, VOLUME_REFERENCE_ANNOTATION_TYPE);
		}
		System.out.println("TIME: Volume references cleaned up after " + (System.currentTimeMillis() - start) + "ms");
//		
//		/* TODOnot
//Prevent non-filtered title numbers mistaken for page numbers:
//- gather stats on non-excluded word blocks and detail elements found after pagination
//- reset references whose paginations fall out of order ...
//- ... and re-assess title-JoP split
//- accept a pagination ahead of an editor list or volume reference label or volume title, as that actually happens ("<authorList><year>?<title><pagination>In: <editorList><volumeTitle><publisher><year>?")
//- reject a pagination ahead of a JoP if not observed in multiple non-questionable references
//- increase probability of rejection if (a) single page or (b) page range short (2-3), and (c) page number is valid year or (d) page range is valid range of years, with years falling into colonial age (1800-1950, and even more probable 1850-1914)
//==> helps catch "... Aus bus Doe 19xx ..." and "... Aus bus Doe, 19xx ..."
//==> helps catch "... Doe Expedition to Anywhere 19xx-19xy ..."
//		 */
//		CountingSet numberDetailEnvironments = new CountingSet(new TreeMap());
//		CountingSet ndbNumberDetailEnvironments = new CountingSet(new TreeMap());
//		CountingSet nonNdbNumberDetailEnvironments = new CountingSet(new TreeMap());
//		HashSet[] refNumberDetailEnvironments = new HashSet[bibRefs.length];
//		start = System.currentTimeMillis();
//		//	TODOnot make this a separate method, e.g. collectNumberDetailEnvitonments(BibRef[] bibRefs)
//		for (int r = 0; r < bibRefs.length; r++) {
//			refNumberDetailEnvironments[r] = new HashSet(); // use set to eliminate duplicates inside individual references
//			if (bibRefs[r].volumeDesignator != null)
//				this.addAnnotationEnvironment(bibRefs[r], bibRefs[r].volumeDesignator, "part", refNumberDetailEnvironments[r]);
//			if (bibRefs[r].issueDesignator != null)
//				this.addAnnotationEnvironment(bibRefs[r], bibRefs[r].issueDesignator, "part", refNumberDetailEnvironments[r]);
//			if (bibRefs[r].pagination != null)
//				this.addAnnotationEnvironment(bibRefs[r], bibRefs[r].pagination, "pagination", refNumberDetailEnvironments[r]);
//			
//			//	aggregate over references
//			numberDetailEnvironments.addAll(refNumberDetailEnvironments[r]);
//			if (bibRefs[r].numberDetailBlock == null)
//				nonNdbNumberDetailEnvironments.addAll(refNumberDetailEnvironments[r]);
//			else ndbNumberDetailEnvironments.addAll(refNumberDetailEnvironments[r]);
//		}
//		System.out.println("TIME: Part designators environments collected after " + (System.currentTimeMillis() - start) + "ms");
//		if (DEBUG) {
//			System.out.println("Number detail environments:");
//			for (Iterator ndeit = numberDetailEnvironments.iterator(); ndeit.hasNext();) {
//				String nde = ((String) ndeit.next());
//				System.out.println(" - " + nde + " (in " + numberDetailEnvironments.getCount(nde) + " of " + bibRefs.length + " references, " + ndbNumberDetailEnvironments.getCount(nde) + " with number detail block, " + nonNdbNumberDetailEnvironments.getCount(nde) + " without)");
//			}
//		}
//		
//		//	TODOnot collect reverse orders, and clean up orders that don't reverse (they only obscure the scores)
//		Properties numberDetailOrderReverses = new Properties();
//		for (Iterator ndeit = numberDetailEnvironments.iterator(); ndeit.hasNext();) {
//			String nde = ((String) ndeit.next());
//			if (nde.startsWith("__") || nde.endsWith("__"))
//				continue; // let's not reverse wildcarded environments
//			if (!nde.matches("[a-zA-Z\\_]+"))
//				continue; // let's hold on to punctuation
//			String[] ndeParts = nde.split("\\_");
//			if (ndeParts.length != 2)
//				continue; // let's not reverse full environment
//			String rNde = (ndeParts[1] + "_" + ndeParts[0]);
//			if (numberDetailEnvironments.contains(rNde)) {
//				numberDetailOrderReverses.setProperty(nde, rNde);
//				numberDetailOrderReverses.setProperty(rNde, nde);
//			}
//			else {
//				ndeit.remove();
//				ndbNumberDetailEnvironments.removeAll(nde);
//				nonNdbNumberDetailEnvironments.removeAll(nde);
//			}
////			if (!ndbNumberDetailEnvironments.contains(rNde))
////				ndbNumberDetailEnvironments.removeAll(nde);
////			if (!nonNdbNumberDetailEnvironments.contains(rNde))
////				nonNdbNumberDetailEnvironments.removeAll(nde);
//		}
//		
//		//	TODOnot score part designator and pagination positions
//		//	TODOnot make this a separate method
//		for (int r = 0; r < bibRefs.length; r++) {
//			if (bibRefs[r].preExistingStructure)
//				continue;
//			if (DEBUG) System.out.println("Scoring part designators and pagination in " + bibRefs[r].annotation.toXML());
//			if (bibRefs[r].volumeDesignator != null)
//				this.scoreAnnotationByEnvironment(bibRefs[r].volumeDesignator, "part", refNumberDetailEnvironments[r], numberDetailEnvironments, numberDetailOrderReverses, ndbNumberDetailEnvironments, nonNdbNumberDetailEnvironments);
//			if (bibRefs[r].issueDesignator != null)
//				this.scoreAnnotationByEnvironment(bibRefs[r].issueDesignator, "part", refNumberDetailEnvironments[r], numberDetailEnvironments, numberDetailOrderReverses, ndbNumberDetailEnvironments, nonNdbNumberDetailEnvironments);
//			if (bibRefs[r].pagination != null)
//				this.scoreAnnotationByEnvironment(bibRefs[r].pagination, "pagination", refNumberDetailEnvironments[r], numberDetailEnvironments, numberDetailOrderReverses, ndbNumberDetailEnvironments, nonNdbNumberDetailEnvironments);
//		}
		
		//	guess type and set respective annotation attribute
		pm.setStep("Classifying references");
		pm.setBaseProgress(90);
		pm.setMaxProgress(95);
		start = System.currentTimeMillis();
		for (int r = 0; r < bibRefs.length; r++) {
			pm.setProgress((r * 100) / bibRefs.length);
			if (bibRefs[r].type != null)
				continue;
			this.classify(bibRefs[r]);
		}
		System.out.println("TIME: References classified after " + (System.currentTimeMillis() - start) + "ms");
		
		//	further split or classify origin (not in volume references, as main call gets here after returning from integrated recursion, and generic origin passes on more easily)
		if (detailOrigin) {
			pm.setStep("Parsing publishers");
			pm.setBaseProgress(93);
			pm.setMaxProgress(98);
			start = System.currentTimeMillis();
			for (int r = 0; r < bibRefs.length; r++) {
				pm.setProgress((r * 100) / bibRefs.length);
				this.parseOrigin(bibRefs[r], primarySeparator);
			}
			System.out.println("TIME: Origins parsed after " + (System.currentTimeMillis() - start) + "ms");
		}
		
		//	transfer annotations to references
		pm.setStep("Annotating details");
		pm.setBaseProgress(95);
		pm.setMaxProgress(100);
		start = System.currentTimeMillis();
		for (int r = 0; r < bibRefs.length; r++) {
			pm.setProgress((r * 100) / bibRefs.length);
			if (bibRefs[r].preExistingStructure)
				continue;
			this.annotateDetails(bibRefs[r]);
		}
		System.out.println("TIME: Details annotated after " + (System.currentTimeMillis() - start) + "ms");
		
		//	finally ...
		return authorListStyle;
	}
	
	private boolean filterNumberDetailsByDetailOrder(BibRef bibRef, String[] detailTypes) {
		boolean detailsChangedInRound;
		boolean detailsChanged = false;
		
		//	keep going as long as anything changes
		do {
			detailsChangedInRound = false;
			if (this.filterNumberDetailByDetailOrder(bibRef, bibRef.volumeDesignator, detailTypes)) {
				bibRef.volumeDesignator = null;
				detailsChangedInRound = true;
			}
			if (this.filterNumberDetailByDetailOrder(bibRef, bibRef.issueDesignator, detailTypes)) {
				bibRef.issueDesignator = null;
				detailsChangedInRound = true;
			}
			if (this.filterNumberDetailByDetailOrder(bibRef, bibRef.numberDesignator, detailTypes)) {
				bibRef.numberDesignator = null;
				detailsChangedInRound = true;
			}
			if (this.filterNumberDetailByDetailOrder(bibRef, bibRef.pagination, detailTypes)) {
				bibRef.pagination = null;
				detailsChangedInRound = true;
			}
			detailsChanged |= detailsChangedInRound;
		}
		while (detailsChangedInRound);
		
		//	report result
		return detailsChanged;
	}
	
	private boolean filterNumberDetailByDetailOrder(BibRef bibRef, Annotation detail, String[] detailTypes) {
		if (detail == null)
			return false;
		if (DEBUG) System.out.println(" - checking " + detail.toXML());
		
		//	collect detail types surrounding argument detail
		HashSet detailTypesAll = new HashSet();
		for (int t = 0; t < bibRef.annotation.size(); t++) {
			if (!"_".equals(detailTypes[t]))
				detailTypesAll.add(detailTypes[t]);
		}
		
		//	collect detail types surrounding argument detail
		HashSet detailTypesBefore = new HashSet();
		String detailTypeBefore = null;
		for (int t = 0; t < detail.getStartIndex(); t++) {
			if (!"_".equals(detailTypes[t]))
				detailTypesBefore.add(detailTypes[t]);
			detailTypeBefore = detailTypes[t];
		}
		HashSet detailTypesAfter = new HashSet();
		String detailTypeAfter = null;
		for (int t = (bibRef.annotation.size() - 1); t >= detail.getEndIndex(); t--) {
			if (!"_".equals(detailTypes[t]))
				detailTypesAfter.add(detailTypes[t]);
			detailTypeAfter = detailTypes[t];
		}
		
		//	collect surrounding punctuation
		String punctuationBefore = (((detail.getStartIndex() != 0) && Gamta.isPunctuation(bibRef.annotation.valueAt(detail.getStartIndex()-1))) ? bibRef.annotation.valueAt(detail.getStartIndex()-1) : null);
		String punctuationAfter = (((detail.getEndIndex() < bibRef.annotation.size()) && Gamta.isPunctuation(bibRef.annotation.valueAt(detail.getEndIndex()))) ? bibRef.annotation.valueAt(detail.getEndIndex()) : null);
		
		//	check detail for removal or re-designation
		String newDetailType = null;
		
		//	remove any part designator or pagination following after URL or DOI (unless also followed by authors): those guys usually come after the actual details, unless they are at the very start of a reference (never seen the latter, but it's conceivable)
		if (detailTypesBefore.contains(PUBLICATION_URL_ANNOTATION_TYPE) || detailTypesBefore.contains(PUBLICATION_DOI_ANNOTATION_TYPE)) {
			newDetailType = "_";
			if (DEBUG) System.out.println("   ==> removed for preceding URL or DOI");
		}
		
		//	remove any part designators that ...
		else if (PART_DESIGNATOR_ANNOTATION_TYPE.equals(detail.getType())) {
			
			//	... precede JoP (new word block filters should prevent square bracket comments mistaken for JoP): "<volume> of <journal>" should be pretty rare ...
			if (detailTypesAfter.contains(JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE) || detailTypesAfter.contains(JOURNAL_NAME_ANNOTATION_TYPE)) {
				newDetailType = "_";
				if (DEBUG) System.out.println("   ==> removed for preceding journal name");
			}
			
			//	... occur in the absence of any journal name
			else if (!detailTypesBefore.contains(JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE) && !detailTypesBefore.contains(JOURNAL_NAME_ANNOTATION_TYPE)) {
				newDetailType = "_";
				if (DEBUG) System.out.println("   ==> removed for absence of journal name");
			}
		}
		
		//	handle paginations in presence of volume reference
		else if ((bibRef.volumeReference != null) || detailTypesAll.contains(VOLUME_TITLE_ANNOTATION_TYPE) || detailTypesAll.contains(EDITOR_ANNOTATION_TYPE)) {
			
		}
		
		//	handle paginations in absence of volume reference
		else {
			
			//	re-designate single page number immediately preceded by JoP as part designator in absence of both volume reference and other part designator: a journal volume is a lot more of a citable entity than a single untitled page in a book ...
			if ((detail.size() == 1) && detail.firstValue().matches("[1-9][0-9]*") && !detailTypesAll.contains(PART_DESIGNATOR_ANNOTATION_TYPE) && (JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE.equals(detailTypeBefore) || JOURNAL_NAME_ANNOTATION_TYPE.equals(detailTypeBefore))) {
				newDetailType = PART_DESIGNATOR_ANNOTATION_TYPE;
				detail.changeTypeTo(PART_DESIGNATOR_ANNOTATION_TYPE);
				detail.setAttribute(TYPE_ATTRIBUTE, VOLUME_DESIGNATOR_TYPE);
				bibRef.volumeDesignator = detail;
				if (DEBUG) System.out.println("   ==> re-designated as part designator");
			}
			
			//	remove if preceding part designator or JoP in absence of volume reference: "pp. <pagination> In: <editors>? <volumeTitle> <journal> <volume>" does occur, as does "pp. <pagination> In: <editors>? <volumeTitle> <publisher>", but "pp. <pagination> in <journal> <volume>" should be pretty rare ...
			else if (detailTypesAfter.contains(PART_DESIGNATOR_ANNOTATION_TYPE) || detailTypesAfter.contains(JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE) || detailTypesAfter.contains(JOURNAL_NAME_ANNOTATION_TYPE) || detailTypesAfter.contains(PUBLISHER_ANNOTATION_TYPE) || detailTypesAfter.contains(LOCATION_ANNOTATION_TYPE)) {
				newDetailType = "_";
				if (DEBUG) System.out.println("   ==> removed for preceding part designator, journal name, or publisher");
			}
			
			//	remove single page numbers if both volume reference (editors and/or volume title) and part designator absent (proceedings titles come out as volume title): that page has to be part of just something ... (retain page ranges though, as they are too distinctive to stray, and proceedings titles might not always be recognized as such)
			else if ((detail.size() == 1) && !detailTypesAll.contains(PART_DESIGNATOR_ANNOTATION_TYPE)) {
				newDetailType = "_";
				if (DEBUG) System.out.println("   ==> removed for absence of part designator and volume reference");
			}
		}
		
		//	anything to change?
		if (newDetailType == null)
			return false;
		
		//	adjust detail types (detail annotation will be removed in caller)
		for (int t = detail.getStartIndex(); t < detail.getEndIndex(); t++)
			detailTypes[t] = newDetailType;
		return true;
	}
//	
//	private void addAnnotationEnvironment(BibRef bibRef, Annotation annot, String type, HashSet environment) {
//		
//		//	count all element orders
//		for (int t = 0; t < annot.getStartIndex(); t++) {
//			if (!"_".equals(bibRef.structure.details[t]))
//				environment.add(bibRef.structure.details[t] + "_" + type);
//		}
//		for (int t = annot.getEndIndex(); t < bibRef.annotation.size(); t++) {
//			if (!"_".equals(bibRef.structure.details[t]))
//				environment.add(type + "_" + bibRef.structure.details[t]);
//		}
//		
//		//	get punctuation and element before
////		if ((bibRefs[r].volumeDesignator.getStartIndex() != 0) && "_".equals(bibRefs[r].structure.details[bibRefs[r].volumeDesignator.getStartIndex()-1]) && Gamta.isPunctuation(bibRefs[r].annotation.valueAt(bibRefs[r].volumeDesignator.getStartIndex()-1)))
//		String punctBefore = null;
//		if (annot.getStartIndex() != 0) {
//			if (Gamta.isPunctuation(bibRef.annotation.valueAt(annot.getStartIndex()-1))) {
//				punctBefore = bibRef.annotation.valueAt(annot.getStartIndex()-1);
//				environment.add(punctBefore + "_" + type);
//			}
//			else punctBefore = "_";
//			environment.add("$_" + type);
//		}
//		String elementBefore = null;
//		for (int t = (annot.getStartIndex()-1); t >= 0; t--) {
//			if ("_".equals(bibRef.structure.details[t]))
//				continue;
//			if (type.equals(bibRef.structure.details[t]))
//				continue;
//			elementBefore = bibRef.structure.details[t];
//			break;
//		}
//		
//		//	get punctuation and element after
////		if ((bibRefs[r].volumeDesignator.getEndIndex() < bibRefs[r].annotation.size()) && "_".equals(bibRefs[r].structure.details[bibRefs[r].volumeDesignator.getEndIndex()]) && Gamta.isPunctuation(bibRefs[r].annotation.valueAt(bibRefs[r].volumeDesignator.getEndIndex())))
//		String punctAfter = null;
//		if (annot.getEndIndex() < bibRef.annotation.size()) {
//			if (Gamta.isPunctuation(bibRef.annotation.valueAt(annot.getEndIndex()))) {
//				punctAfter = bibRef.annotation.valueAt(annot.getEndIndex());
//				environment.add(type + "_" + punctAfter);
//			}
//			environment.add(type + "_$");
//		}
//		String elementAfter = null;
//		for (int t = annot.getEndIndex(); t < bibRef.annotation.size(); t++) {
//			if ("_".equals(bibRef.structure.details[t]))
//				continue;
//			if (type.equals(bibRef.structure.details[t]))
//				continue;
//			elementAfter = bibRef.structure.details[t];
//			break;
//		}
//		
//		//	add combinations of surrounding elements and punctuation
//		environment.add(elementBefore + "_" + type + "_" + elementAfter);
//		environment.add(punctBefore + "_" + type + "_" + elementAfter);
//		environment.add(elementBefore + "_" + type + "_" + punctAfter);
//		environment.add(punctBefore + "_" + type + "_" + punctAfter);
//		
//		//	keep occurrence count
//		environment.add("$_" + type + "_$");
//	}
//	
//	private void scoreAnnotationByEnvironment(Annotation annot, String type, HashSet refNumberDetailEnvironments, CountingSet numberDetailEnvironments, Properties numberDetailOrderReverses, CountingSet ndbNumberDetailEnvironments, CountingSet nonNdbNumberDetailEnvironments) {
//		if (DEBUG) System.out.println(" - scoring number detail " + annot.toXML());
//		int score = 0;
//		int lScore = 0;
//		int tScore = 0;
//		int eScore = 0;
//		int ndbScore = 0;
//		int nonNdbScore = 0;
//		float pScore = 0;
//		float lpScore = 0;
//		float tpScore = 0;
//		for (Iterator ndeit = refNumberDetailEnvironments.iterator(); ndeit.hasNext();) {
//			String nde = ((String) ndeit.next());
//			if (nde.startsWith("$_") || nde.endsWith("_$"))
//				continue; // don't score overall occurrence counts
//			if (!nde.startsWith(type + "_") && !nde.endsWith("_" + type) && (nde.indexOf("_" + type + "_") == -1))
//				continue; // this one's not relevant
//			if (!numberDetailEnvironments.contains(nde))
//				continue; // eliminated as one-sided
//			if (DEBUG) System.out.println("   - " + nde + " (in " + (numberDetailEnvironments.getCount(nde) - 1) + " other refs)");
//			
//			//	score occurrences of element order
//			if (nde.matches("[a-zA-Z\\_]+") || (nde.indexOf("_" + type + "_") != -1)) {
//				score += (numberDetailEnvironments.getCount(nde) - 1);
//				if (nde.startsWith(type + "_"))
//					tScore += (numberDetailEnvironments.getCount(nde) - 1);
//				else if (nde.endsWith("_" + type))
//					lScore += (numberDetailEnvironments.getCount(nde) - 1);
//				else eScore += (numberDetailEnvironments.getCount(nde) - 1);
//				ndbScore += (ndbNumberDetailEnvironments.getCount(nde) - 1);
//				nonNdbScore += (nonNdbNumberDetailEnvironments.getCount(nde) - 1);
//				
//				//	reduce by frequency of reverse element order
//				String rNde = numberDetailOrderReverses.getProperty(nde);
//				if ((rNde != null) && !nde.equals(rNde)) {
//					if (DEBUG) System.out.println("     " + rNde + " (in " + numberDetailEnvironments.getCount(rNde) + " other refs)");
//					score -= numberDetailEnvironments.getCount(rNde);
//					ndbScore -= ndbNumberDetailEnvironments.getCount(rNde);
//					nonNdbScore -= nonNdbNumberDetailEnvironments.getCount(rNde);
//					if (nde.startsWith(type + "_"))
//						tScore -= numberDetailEnvironments.getCount(rNde);
//					else if (nde.endsWith("_" + type))
//						lScore -= numberDetailEnvironments.getCount(rNde);
//					else eScore -= numberDetailEnvironments.getCount(rNde);
//				}
//			}
//			
//			//	score punctuation as fraction of all occurrences
//			else {
//				int pRefCount = numberDetailEnvironments.getCount(nde.startsWith(type + "_") ? (type + "_$") : ("$_" + type));
//				pScore += (((float) (numberDetailEnvironments.getCount(nde) - 1)) / pRefCount);
//				if (nde.startsWith(type + "_"))
//					tpScore += (((float) (numberDetailEnvironments.getCount(nde) - 1)) / pRefCount);
//				else if (nde.endsWith("_" + type))
//					lpScore += (((float) (numberDetailEnvironments.getCount(nde) - 1)) / pRefCount);
//			}
//		}
//		if (DEBUG) System.out.println("   ==> scored " + score + " (" + lScore + " lead, " + tScore + " tail, " + eScore + " env, " + pScore + " punct, " + lpScore + " lead-punct, " + tpScore + " tail-punct, " + ndbScore + " with number detail block, " + nonNdbScore + " without)");
//	}
	
	private boolean hasCapWord(Annotation wordBlock) {
		String bracket = null;
		for (int t = 0; t < wordBlock.size(); t++) {
			String v = wordBlock.valueAt(t);
			if (bracket != null) {
				if (Gamta.closes(v, bracket))
					bracket = null;
				continue;
			}
			if (Gamta.isOpeningBracket(v)) {
				bracket = v;
				continue;
			}
			if (v.length() < 2)
				continue;
			if (this.journalPublisherStopWords.containsIgnoreCase(v))
				continue;
			if (Gamta.isRomanNumber(v))
				continue;
			if (Character.toLowerCase(v.charAt(0)) == v.charAt(0))
				continue;
			for (int c = 0; c < v.length(); c++) {
				if ("AEIOUYaeiouy".indexOf(v.charAt(c)) != -1)
					return true;
			}
		}
		return false;
	}
//	
//	private boolean hasVowel(Annotation annot) {
//		for (int t = 0; t < annot.size(); t++) {
//			String v = annot.valueAt(t);
//			for (int c = 0; c < v.length(); c++) {
//				if ("AEIOUYaeiouy".indexOf(v.charAt(c)) != -1)
//					return true;
//			}
//		}
//		return false;
//	}
	
	private Annotation[] getKnownJops(BibRef bibRef) {
		ArrayList knownJopList = new ArrayList();
		if (DEBUG) System.out.println("Getting known journals/publishers from " + bibRef.annotation.toXML());
		
		//	do lexicon lookups (not first block, that one's definitely part of the title)
		if (DEBUG) System.out.println("  - journal/publisher names from dictionary:");
		for (int b = 1; b < bibRef.wordBlocks.length; b++) {
			if (!this.hasCapWord(bibRef.wordBlocks[b]))
				continue;
			if (this.knownJournalsAndPublishers.lookup(TokenSequenceUtils.concatTokens(bibRef.wordBlocks[b], true, true))) {
				if (DEBUG) System.out.println("    - " + bibRef.wordBlocks[b]);
				bibRef.wordBlocks[b].setAttribute("isKnown", "true");
				knownJopList.add(bibRef.wordBlocks[b]);
			}
			for (int l = (b+1); l < bibRef.wordBlocks.length; l++) {
				if ((bibRef.wordBlocks[l].getStartIndex() - bibRef.wordBlocks[l-1].getEndIndex()) > 1)
					break;
				if (this.knownJournalsAndPublishers.lookup(TokenSequenceUtils.concatTokens(bibRef.annotation, bibRef.wordBlocks[b].getStartIndex(), (bibRef.wordBlocks[l].getEndIndex() - bibRef.wordBlocks[b].getStartIndex()), true, true))) {
					Annotation knownJop = Gamta.newAnnotation(bibRef.annotation, null, bibRef.wordBlocks[b].getStartIndex(), (bibRef.wordBlocks[l].getEndIndex() - bibRef.wordBlocks[b].getStartIndex()));
					if (DEBUG) System.out.println("    - " + knownJop);
					knownJop.setAttribute("isKnown", "true");
					knownJopList.add(knownJop);
				}
			}
		}
		
		Collections.sort(knownJopList);
		return ((Annotation[]) knownJopList.toArray(new Annotation[knownJopList.size()]));
	}
	
	private Annotation[] getProceedingsTitles(BibRef bibRef) {
		ArrayList knownJopList = new ArrayList();
		
		//	get years (might come from parent reference)
		Annotation[] yearAnnots = ((bibRef.parentRef == null) ? bibRef.years : bibRef.parentRef.years);
		Annotation yearAnnot = ((bibRef.parentRef == null) ? bibRef.year : bibRef.parentRef.year);
		
		//	use pattern to find proceedings title from correct year
		if ((yearAnnots != null) && (yearAnnot != null) && (yearAnnot.length() == 4)) {
			String year = yearAnnot.getValue();
			String yearRegEx;
			if (yearAnnots.length > 1)
				yearRegEx = (year + "|\\'?" + year.substring(2));
			else yearRegEx = ("\\'?" + year.substring(2));
			Annotation[] proceedingsTitles = Gamta.extractAllMatches(bibRef.annotation, ("(Proc(\\.|eedings))[^0-9]+(" + yearRegEx + ")"), true);
			if (DEBUG) {
				System.out.println("  - proceedings titles for year " + year + ":");
				for (int p = 0; p < proceedingsTitles.length; p++)
					System.out.println("    - " + proceedingsTitles[p]);
			}
			if (proceedingsTitles.length == 0) try {
				year = ("" + (Integer.parseInt(yearAnnot.getValue()) - 1));
				if (yearAnnots.length > 1)
					yearRegEx = (year + "|\\'?" + year.substring(2));
				else yearRegEx = ("\\'?" + year.substring(2));
				proceedingsTitles = Gamta.extractAllMatches(bibRef.annotation, ("(Proc(\\.|eedings))[^0-9]+(" + yearRegEx + ")"), true);
				if (DEBUG) {
					System.out.println("  - proceedings titles for year " + year + ":");
					for (int p = 0; p < proceedingsTitles.length; p++)
						System.out.println("    - " + proceedingsTitles[p]);
				}
			} catch (NumberFormatException nfe) {}
			for (int p = 0; p < proceedingsTitles.length; p++) {
				proceedingsTitles[p].setAttribute("isProceedings", "true");
				knownJopList.add(proceedingsTitles[p]);
			}
		}
		
		Collections.sort(knownJopList);
		return ((Annotation[]) knownJopList.toArray(new Annotation[knownJopList.size()]));
	}
	
	private float getJopScore(Annotation wordBlock) {
		float js = 0;
		int jwc = 0;
		for (int t = 0; t < wordBlock.size(); t++) {
			String v = wordBlock.valueAt(t);
			if (Gamta.isWord(v)) {
				js += this.jopWordStat.getScore(v, (t == 0), ((t+1) == wordBlock.size()));
				jwc++;
			}
		}
		return ((jwc == 0) ? 0 : (js / jwc));
	}
	
	private static class WordUseData {
		String word;
		int count = 0;
		int jopCount = 0;
		int jopStartCount = 0;
		int jopEndCount = 0;
		WordUseData(String word) {
			this.word = word;
		}
		WordUseData(String word, int count, int jopCount, int jopStartCount, int jopEndCount) {
			this.word = word;
			this.count = count;
			this.jopCount = jopCount;
			this.jopStartCount = jopStartCount;
			this.jopEndCount = jopEndCount;
		}
		void count(boolean inJop, boolean jopStart, boolean jopEnd) {
			this.count++;
			if (inJop) {
				this.jopCount++;
				if (jopStart)
					this.jopStartCount++;
				if (jopEnd)
					this.jopEndCount++;
			}
		}
		float getScore(boolean jopStart, boolean jopEnd) {
			if ((this.count == 0) || (this.jopCount == 0))
				return 0;
			return (((float) (this.jopCount + (jopStart ? this.jopStartCount : 0) + (jopEnd ? this.jopEndCount : 0))) / this.count);
		}
		String toDataString() {
			return (this.word + "|" + this.count + "|" + this.jopCount + "|" + this.jopStartCount + "|" + this.jopEndCount);
		}
	}
	private static class WordUseStat {
		TreeMap wordStats = new TreeMap(String.CASE_INSENSITIVE_ORDER);
		boolean dirty = false;
		void count(String word, boolean inJop, boolean jopStart, boolean jopEnd) {
			WordUseData wud = ((WordUseData) this.wordStats.get(word));
			if (wud == null) {
				wud = new WordUseData(word);
				this.wordStats.put(word, wud);
			}
			wud.count(inJop, jopStart, jopEnd);
			this.dirty = true;
		}
		float getScore(String word, boolean jopStart, boolean jopEnd) {
			WordUseData wud = ((WordUseData) this.wordStats.get(word));
			if (wud == null)
				return 0;
			return wud.getScore(jopStart, jopEnd);
		}
		boolean isDirty() {
			return this.dirty;
		}
		void writeData(BufferedWriter bw) throws IOException {
			for (Iterator wit = this.wordStats.keySet().iterator(); wit.hasNext();) {
				WordUseData wud = ((WordUseData) this.wordStats.get(wit.next()));
				bw.write(wud.toDataString());
				bw.newLine();
			}
			bw.flush();
			this.dirty = false;
		}
		void readData(BufferedReader br) throws IOException {
			String dl;
			while ((dl = br.readLine()) != null) {
				String[] d = dl.split("\\|");
				if (d.length == 5)
					this.wordStats.put(d[0], new WordUseData(d[0], Integer.parseInt(d[1]), Integer.parseInt(d[2]), Integer.parseInt(d[3]), Integer.parseInt(d[4])));
			}
		}
	}
	
	private void getWordBlocks(BibRef bibRef, String[] detailTypes) {
		if (DEBUG) System.out.println("Getting word blocks from " + bibRef.annotation.toXML());
		
		//	summarize existing structure for filtering
		bibRef.wordBlockExcluded = new boolean[bibRef.annotation.size()];
		Arrays.fill(bibRef.wordBlockExcluded, false);
		
		//	handle URLs and related patterns
		augmentFilteredTokens(bibRef.wordBlockExcluded, bibRef.urls, "URL");
		augmentFilteredTokens(bibRef.wordBlockExcluded, bibRef.dois, "DOI");
		augmentFilteredTokens(bibRef.wordBlockExcluded, bibRef.labeledDates, "URL access date");
		if ((bibRef.urls.length + bibRef.dois.length) != 0) {
			Annotation[] labeledUrls = this.getLabeledUrls(bibRef);
			augmentFilteredTokens(bibRef.wordBlockExcluded, labeledUrls, "labeled URL");
		}
		
		//	exclude anything following after a URL or DOI
		for (int u = 0; u < bibRef.urls.length; u++) {
			if (bibRef.urls[u].getEndIndex() == bibRef.annotation.size())
				continue;
			Arrays.fill(bibRef.wordBlockExcluded, bibRef.urls[u].getEndIndex(), bibRef.annotation.size(), true);
			if (DEBUG) System.out.println(" - excluding after-URL tokens '" + TokenSequenceUtils.concatTokens(bibRef.annotation, bibRef.urls[u].getEndIndex(), (bibRef.annotation.size() - bibRef.urls[u].getEndIndex()), true, true) + "'");
		}
		for (int d = 0; d < bibRef.dois.length; d++) {
			if (bibRef.dois[d].getEndIndex() == bibRef.annotation.size())
				continue;
			Arrays.fill(bibRef.wordBlockExcluded, bibRef.dois[d].getEndIndex(), bibRef.annotation.size(), true);
			if (DEBUG) System.out.println(" - excluding after-DOI tokens '" + TokenSequenceUtils.concatTokens(bibRef.annotation, bibRef.dois[d].getEndIndex(), (bibRef.annotation.size() - bibRef.dois[d].getEndIndex()), true, true) + "'");
		}
		
		//	handle editor list labels (only if we have a volume reference)
		if (bibRef.volumeRef != null) {
			Annotation[] editorListLabels = Gamta.extractAllMatches(bibRef.annotation, this.editorListLabelRegEx);
			augmentFilteredTokens(bibRef.wordBlockExcluded, editorListLabels, "editor list label");
		}
		
		//	handle other details
		for (int t = 0; t < detailTypes.length; t++)
			if (!"_".equals(detailTypes[t])) {
				if (PART_DESIGNATOR_ANNOTATION_TYPE.equals(detailTypes[t]) && bibRef.annotation.valueAt(t).matches("[A-Zz-z]")) {
					if (DEBUG) System.out.println(" - ignoring part designator letter '" + bibRef.annotation.valueAt(t) + "'");
					continue;
				}
				bibRef.wordBlockExcluded[t] = true;
				if (DEBUG) System.out.println(" - excluding token assigned as " + detailTypes[t] + " '" + bibRef.annotation.valueAt(t) + "'");
			}
		for (int i = 0; i < bibRef.bookContentInfos.size(); i++) {
			Annotation bci = ((Annotation) bibRef.bookContentInfos.get(i));
			augmentFilteredTokens(bibRef.wordBlockExcluded, bci, "book content info");
		}
		
		//	also filter plain book content info labels, but only if not embedded in plain word sequence
		Annotation[] bookContentInfoLabels = Gamta.extractAllContained(bibRef.annotation, this.bookContentInfoNumberingInvalidatorsTailing, true);
		for (int l = 0; l < bookContentInfoLabels.length; l++) {
			boolean nonWordLeft = ((bookContentInfoLabels[l].getStartIndex() > 0) && !Gamta.isWord(bibRef.annotation.valueAt(bookContentInfoLabels[l].getStartIndex() - 1)));
			boolean nonWordRight = ((bookContentInfoLabels[l].getEndIndex() < bibRef.annotation.size()) && !Gamta.isWord(bibRef.annotation.valueAt(bookContentInfoLabels[l].getEndIndex())));
			if (nonWordLeft || nonWordRight)
				augmentFilteredTokens(bibRef.wordBlockExcluded, bookContentInfoLabels[l], "book content info label");
		}
		
		//	handle custom excluded phrases
		Annotation[] wordBlockExcluded = Gamta.extractAllContained(bibRef.annotation, this.wordBlockExcluded, false);
		augmentFilteredTokens(bibRef.wordBlockExcluded, wordBlockExcluded, "custom phrase");
		for (int p = 0; p < this.wordBlockExcludePatterns.size(); p++) {
			wordBlockExcluded = Gamta.extractAllMatches(bibRef.annotation, this.wordBlockExcludePatterns.get(p), false);
			augmentFilteredTokens(bibRef.wordBlockExcluded, wordBlockExcluded, "custom pattern phrase");
		}
		
		//	assess emphases
		bibRef.boldToken = new boolean[bibRef.annotation.size()];
		Arrays.fill(bibRef.boldToken, false);
		bibRef.italicsToken = new boolean[bibRef.annotation.size()];
		Arrays.fill(bibRef.italicsToken, false);
		Annotation[] emphases = bibRef.annotation.getAnnotations(EMPHASIS_TYPE);
		for (int e = 0; e < emphases.length; e++) {
			Arrays.fill(bibRef.boldToken, emphases[e].getStartIndex(), emphases[e].getEndIndex(), emphases[e].hasAttribute(BOLD_ATTRIBUTE));
			Arrays.fill(bibRef.italicsToken, emphases[e].getStartIndex(), emphases[e].getEndIndex(), emphases[e].hasAttribute(ITALICS_ATTRIBUTE));
			if (DEBUG) System.out.println(" - got emphasis (" + (emphases[e].hasAttribute(BOLD_ATTRIBUTE) ? "B" : "") + (emphases[e].hasAttribute(ITALICS_ATTRIBUTE) ? "I" : "") + ") connected phrase '" + emphases[e].getValue() + "'");
		}
		
		//	get word blocks
		ArrayList wordBlocks = new ArrayList();
		
		//	we've seen this one before, use what's there
		if (bibRef.preExistingStructure) {
			wordBlocks.addAll(Arrays.asList(bibRef.annotation.getAnnotations(TITLE_ANNOTATION_TYPE)));
			wordBlocks.addAll(Arrays.asList(bibRef.annotation.getAnnotations(VOLUME_TITLE_ANNOTATION_TYPE)));
			wordBlocks.addAll(Arrays.asList(bibRef.annotation.getAnnotations(JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE)));
			wordBlocks.addAll(Arrays.asList(bibRef.annotation.getAnnotations(JOURNAL_NAME_ANNOTATION_TYPE)));
			wordBlocks.addAll(Arrays.asList(bibRef.annotation.getAnnotations(SERIES_IN_JOURNAL_ANNOTATION_TYPE)));
			wordBlocks.addAll(Arrays.asList(bibRef.annotation.getAnnotations(PUBLISHER_ANNOTATION_TYPE)));
			wordBlocks.addAll(Arrays.asList(bibRef.annotation.getAnnotations(LOCATION_ANNOTATION_TYPE)));
		}
		
		//	this one's new
		else {
			
			//	get abbreviation blocks as a whole
			wordBlocks.addAll(Arrays.asList(this.getTitleCaseAbbreviationBlocks(bibRef.annotation, bibRef.wordBlockExcluded)));
			
			//	get word blocks delimited by punctuation
			int wordBlockStart = -1;
			for (int t = 0; t < bibRef.annotation.size(); t++) {
				if (DEBUG && bibRef.wordBlockExcluded[t])
					System.out.println(" - skipping over non-title token '" + bibRef.annotation.valueAt(t) + "'");
				if (Gamta.isPunctuation(bibRef.annotation.valueAt(t)) || bibRef.wordBlockExcluded[t]) {
					if (wordBlockStart != -1)
						wordBlocks.add(Gamta.newAnnotation(bibRef.annotation, null, wordBlockStart, (t-wordBlockStart)));
					wordBlockStart = -1;
				}
				else if (wordBlockStart == -1)
					wordBlockStart = t;
			}
			if (wordBlockStart != -1)
				wordBlocks.add(Gamta.newAnnotation(bibRef.annotation, null, wordBlockStart, (bibRef.annotation.size()-wordBlockStart)));
			
			//	sort out blocks consisting of punctuation marks only, and individual lower case letters
			for (int w = 0; w < wordBlocks.size(); w++) {
				Annotation wb = ((Annotation) wordBlocks.get(w));
				boolean punctuationOnly = true;
				for (int t = wb.getStartIndex(); t < wb.getEndIndex(); t++) {
					String v = bibRef.annotation.valueAt(t);
					if ((Gamta.isWord(v) && !v.matches("[a-z]")) || Gamta.isNumber(v)) {
						punctuationOnly = false;
						break;
					}
				}
				if (punctuationOnly) {
					if (DEBUG) System.out.println(" - removing punctuation-only word block '" + wb.getValue() + "'");
					wordBlocks.remove(w--);
				}
			}
			
			//	truncate leading single Latin lower case letter if preceded by year and followed by capitalized word
			for (int w = 0; w < wordBlocks.size(); w++) {
				Annotation wb = ((Annotation) wordBlocks.get(w));
				if (wb.size() < 2)
					continue;
				if (wb.getStartIndex() < 1)
					continue;
				if (!wb.firstValue().matches("[a-z]"))
					continue;
				if (!wb.valueAt(1).matches("[A-Z].*"))
					continue;
				if (!bibRef.annotation.valueAt(wb.getStartIndex()-1).matches("[12][0-9]{3}"))
					continue;
				if (DEBUG) System.out.println(" - truncating index letter off word block '" + wb.getValue() + "'");
				wb = Gamta.newAnnotation(bibRef.annotation, null, (wb.getStartIndex() + 1), (wb.size() - 1));
				wordBlocks.set(w, wb);
				if (DEBUG)
					System.out.println("   --> '" + wb.getValue() + "'");
			}
			
			//	sort out blocks covered by others
			Collections.sort(wordBlocks);
			for (int w = 1; w < wordBlocks.size(); w++) {
				Annotation owb = ((Annotation) wordBlocks.get(w-1));
				Annotation iwb = ((Annotation) wordBlocks.get(w));
				if (AnnotationUtils.liesIn(iwb, owb))
					wordBlocks.remove(w--);
			}
			
			//	get blocks in brackets (and double quotes, too) as a whole
			Annotation[] bracketBlocks = this.getBracketBlocks(bibRef, bibRef.wordBlockExcluded, detailTypes);
			
			//	sort out plain word blocks covered by ones in brackets
			for (int w = 0; w < wordBlocks.size(); w++) {
				Annotation wb = ((Annotation) wordBlocks.get(w));
				for (int b = 0; b < bracketBlocks.length; b++)
					if (AnnotationUtils.overlaps(wb, bracketBlocks[b])) {
						wb = null;
						break;
					}
				if (wb == null)
					wordBlocks.remove(w--);
			}
			
			//	add blocks in brackets
			wordBlocks.addAll(Arrays.asList(bracketBlocks));
			Collections.sort(wordBlocks);
			
			//	count word blocks in volume reference (got to make sure at least two remain)
			int volumeRefStartIndex = -1;
			int volumeRefWordBlocks = 0;
			if (bibRef.volumeRef != null) {
				volumeRefStartIndex = bibRef.volumeRef.annotation.getStartIndex();
				for (int w = 0; w < wordBlocks.size(); w++) {
					Annotation wb = ((Annotation) wordBlocks.get(w));
					if (volumeRefStartIndex <= wb.getStartIndex())
						volumeRefWordBlocks++;
				}
			}
			
			//	merge immediately adjacent blocks, and ones with exactly one punctuation mark in between that is very rare as a field separator, as well as ones emphasized together
			for (int w = 1; w < wordBlocks.size(); w++) {
				Annotation lwb = ((Annotation) wordBlocks.get(w-1));
				Annotation rwb = ((Annotation) wordBlocks.get(w));
				boolean merge = false;
				
				//	merge immediately adjacent blocks 
				if (rwb.getStartIndex() <= lwb.getEndIndex())
					merge = true;
				
				//	merge over single punctuation mark that is very rare as a field separator
				else if (((rwb.getStartIndex() - lwb.getEndIndex()) == 1) && (":&+/".indexOf(bibRef.annotation.valueAt(lwb.getEndIndex())) != -1))
					merge = true;
				
				//	merge inside continuous emphases
				else if (emphases.length != 0) {
					merge = (bibRef.boldToken[lwb.getStartIndex()] || bibRef.italicsToken[lwb.getStartIndex()]);
					for (int t = (lwb.getStartIndex() + 1); t < rwb.getEndIndex(); t++) {
						if (bibRef.boldToken[t-1] != bibRef.boldToken[t]) {
							merge = false;
							break;
						}
						if (bibRef.italicsToken[t-1] != bibRef.italicsToken[t]) {
							merge = false;
							break;
						}
					}
					
					//	inside volume reference (if present), merge for emphasis only if we have at least two word blocks remaining after merger
					merge = (merge && ((volumeRefStartIndex == -1) || (lwb.getStartIndex() < volumeRefStartIndex) || (volumeRefWordBlocks > 2)));
				}
				
				//	perform merger
				if (merge) {
					Annotation mwb = Gamta.newAnnotation(bibRef.annotation, null, lwb.getStartIndex(), (rwb.getEndIndex() - lwb.getStartIndex()));
					wordBlocks.set((w-1), mwb);
					wordBlocks.remove(w--);
					if ((volumeRefStartIndex != -1) && (volumeRefStartIndex <= mwb.getStartIndex()))
						volumeRefWordBlocks--;
				}
			}
			
			//	TODO also sort out lone numbers leading in reference
			for (int w = 0; w < wordBlocks.size(); w++) {
				Annotation wb = ((Annotation) wordBlocks.get(w));
				if ((wb.size() == 1) && Gamta.isNumber(wb.firstValue()))
					wordBlocks.remove(w--);
			}
			
			//	remove leading 'et al' word blocks (might overrun from author list if no year before title)
			while (wordBlocks.size() != 0) {
				Annotation wb = ((Annotation) wordBlocks.get(0));
				if ("et al".equals(TokenSequenceUtils.concatTokens(wb, true, true)))
					wordBlocks.remove(0);
				else break;
			}
		}
		
		//	sort and return what we have
		Collections.sort(wordBlocks);
		bibRef.wordBlocks = ((Annotation[]) wordBlocks.toArray(new Annotation[wordBlocks.size()]));
	}
	
	private Annotation[] getBracketBlocks(BibRef bibRef, boolean[] isNonTitle, String[] detailTypes) {
		if (DEBUG) System.out.println("Getting bracketed / quoted blocks from " + bibRef.annotation.toXML());
		
		//	find blocks in brackets
		Annotation[] bracketBlocks;
		ArrayList bracketBlockList = new ArrayList();
		bracketBlocks = Gamta.extractAllMatches(bibRef.annotation, "\\([A-Za-z1-9][^\\)]+\\)", true, true, true);
		bracketBlockList.addAll(Arrays.asList(bracketBlocks));
		bracketBlocks = Gamta.extractAllMatches(bibRef.annotation, "\\[[A-Za-z1-9][^\\]]+\\]", true, true, true);
		bracketBlockList.addAll(Arrays.asList(bracketBlocks));
		bracketBlocks = Gamta.extractAllMatches(bibRef.annotation, "\\{[A-Za-z1-9][^\\}]+\\}", true, true, true);
		bracketBlockList.addAll(Arrays.asList(bracketBlocks));
		bracketBlocks = Gamta.extractAllMatches(bibRef.annotation, "\\\"[A-Za-z1-9][^\\\"]+\\\"", true, true, true);
		bracketBlockList.addAll(Arrays.asList(bracketBlocks));
		bracketBlocks = ((Annotation[]) bracketBlockList.toArray(new Annotation[bracketBlockList.size()]));
		bracketBlockList.clear();
		Arrays.sort(bracketBlocks);
		
		//	filter out blocks already assigned
		for (int b = 0; b < bracketBlocks.length; b++) {
			if (DEBUG) System.out.println(" - investigating " + bracketBlocks[b].getValue());
			for (int t = bracketBlocks[b].getStartIndex(); t < bracketBlocks[b].getEndIndex(); t++)
				if (isNonTitle[t]) {
					if (DEBUG) System.out.println("   - interfers with pre-classified or blocked token (" + detailTypes[t] + ") " + bibRef.annotation.valueAt(t));
					bracketBlocks[b] = null;
					break;
				}
			if (bracketBlocks[b] != null) {
				bracketBlockList.add(bracketBlocks[b]);
				if (DEBUG) System.out.println("   ==> retained");
			}
			else if (DEBUG) System.out.println("   ==> discarded");
		}
		if (bracketBlockList.size() < bracketBlocks.length)
			bracketBlocks = ((Annotation[]) bracketBlockList.toArray(new Annotation[bracketBlockList.size()]));
		bracketBlockList.clear();
		
		//	filter out blocks that are included in others
		for (int b = 0; b < bracketBlocks.length; b++) {
			if (bracketBlockList.isEmpty() || !AnnotationUtils.liesIn(bracketBlocks[b], ((Annotation) bracketBlockList.get(bracketBlockList.size()-1))))
				bracketBlockList.add(bracketBlocks[b]);
		}
		
		//	finally ...
		return ((Annotation[]) bracketBlockList.toArray(new Annotation[bracketBlockList.size()]));
	}
	
	private Annotation[] getTitleCaseAbbreviationBlocks(Annotation bibRef, boolean[] isNonTitle) {
		
		//	find abbreviated blocks
		Annotation[] abbreviationBlocks = Gamta.extractAllMatches(bibRef, this.titleCaseAbbreviationBlockRegEx, true, true, false);
		ArrayList abbreviationBlockList = new ArrayList();
		
		//	filter blocks
		for (int b = 0; b < abbreviationBlocks.length; b++) {
			if (DEBUG) System.out.println(" - checking title case abbreviation block '" + abbreviationBlocks[b].getValue() + "'");
			
			//	filter out blocks that do not start right after a punctuation mark (discounting closing brackets)
			String tokenBefore = ((abbreviationBlocks[b].getStartIndex() == 0) ? null : bibRef.valueAt(abbreviationBlocks[b].getStartIndex()-1));
			if ((tokenBefore == null) || !Gamta.isPunctuation(tokenBefore) || Gamta.isClosingBracket(tokenBefore)) {
				abbreviationBlocks[b] = null;
				if (DEBUG) System.out.println("   --> filtered for lack of leading punctuation mark");
				continue;
			}
			
			//	filter out blocks already assigned
			for (int t = abbreviationBlocks[b].getStartIndex(); t < abbreviationBlocks[b].getEndIndex(); t++)
				if (isNonTitle[t]) {
					abbreviationBlocks[b] = null;
					if (DEBUG) System.out.println("   --> filtered for non-title token ('" + bibRef.valueAt(t) + "')");
					break;
				}
			if (abbreviationBlocks[b] == null)
				continue;
			
			//	filter out blocks that include word with more than three vowels
			int maxVowelCount = 0;
			for (int t = 0; t < abbreviationBlocks[b].size(); t++) {
				int vowelCount = 0;
				String v = abbreviationBlocks[b].valueAt(t);
				for (int c = 0; c < v.length(); c++) {
					if ("AEIOUYaeiouy".indexOf(v.charAt(c)) != -1)
						vowelCount++;
				}
				maxVowelCount = Math.max(maxVowelCount, vowelCount);
			}
			if (maxVowelCount > 3) {
				abbreviationBlocks[b] = null;
				if (DEBUG) System.out.println("   --> filtered for excessive vowels (" + maxVowelCount + "):");
				continue;
			}
			
			//	this one looks good thus far
			abbreviationBlockList.add(abbreviationBlocks[b]);
			if (DEBUG) System.out.println("   ==> retained");
		}
//		abbreviationBlocks = ((Annotation[]) abbreviationBlockList.toArray(new Annotation[abbreviationBlockList.size()]));
//		abbreviationBlockList.clear();
//		
//		//	filter out blocks that do not start right after a punctuation mark
//		for (int b = 0; b < abbreviationBlockList.size(); b++) {
//			Annotation ab = ((Annotation) abbreviationBlockList.get(b));
//			if ((ab.getStartIndex() == 0) || !Gamta.isPunctuation(bibRef.valueAt(ab.getStartIndex()-1))) {
//				abbreviationBlockList.remove(b--);
//				if (DEBUG) System.out.println(" - filtered for lack of leading punctuation mark: '" + ab.getValue() + "'");
//			}
//		}
//		abbreviationBlocks = ((Annotation[]) abbreviationBlockList.toArray(new Annotation[abbreviationBlockList.size()]));
//		abbreviationBlockList.clear();
//		
//		//	filter out blocks that include word with more than three vowels
//		for (int b = 0; b < abbreviationBlockList.size(); b++) {
//			Annotation ab = ((Annotation) abbreviationBlockList.get(b));
//			int maxVowelCount = 0;
//			for (int t = 0; t < ab.size(); t++) {
//				int vowelCount = 0;
//				String v = ab.valueAt(t);
//				for (int c = 0; c < v.length(); c++) {
//					if ("AEIOUYaeiouy".indexOf(v.charAt(c)) != -1)
//						vowelCount++;
//				}
//				maxVowelCount = Math.max(maxVowelCount, vowelCount);
//			}
//			if (maxVowelCount > 3) {
//				abbreviationBlockList.remove(b--);
//				if (DEBUG) System.out.println(" - filtered for excessive vowels (" + maxVowelCount + "): '" +ab.getValue() + "'");
//			}
//		}
//		abbreviationBlocks = ((Annotation[]) abbreviationBlockList.toArray(new Annotation[abbreviationBlockList.size()]));
//		abbreviationBlockList.clear();
		
		//	filter out blocks that are included in others
		for (int b = 0; b < abbreviationBlockList.size(); b++) {
			Annotation ab = ((Annotation) abbreviationBlockList.get(b));
			for (int cb = (b+1); cb < abbreviationBlockList.size(); cb++) {
				Annotation cab = ((Annotation) abbreviationBlockList.get(cb));
				if (AnnotationUtils.liesIn(cab, ab)) {
					abbreviationBlockList.remove(cb--);
					if (DEBUG) System.out.println(" - removed for inclusion: '" + cab.getValue() + "'");
				}
			}
		}
		
		//	finally ...
		return ((Annotation[]) abbreviationBlockList.toArray(new Annotation[abbreviationBlockList.size()]));
	}
	
	private void processVolumeRefs(BibRef[] bibRefs, AuthorListStyle authorListStyle, DocumentStyle bibRefStyle, ProgressMonitor pm) {
		ArrayList volumeRefList = new ArrayList();
		for (int r = 0; r < bibRefs.length; r++) {
			MutableAnnotation volumeRef = null;
			MutableAnnotation[] volumeRefs = bibRefs[r].annotation.getMutableAnnotations(VOLUME_REFERENCE_ANNOTATION_TYPE);
			if ((volumeRefs.length != 0) && (volumeRefs[0].size() < bibRefs[r].annotation.size()))
				volumeRef = volumeRefs[0];
			if ((volumeRef == null) && (bibRefs[r].volumeReference != null))
				volumeRef = bibRefs[r].annotation.addAnnotation(bibRefs[r].volumeReference);
			if (volumeRef != null) {
				Object pageId = bibRefs[r].annotation.getAttribute(PAGE_ID_ATTRIBUTE);
				if (pageId != null)
					volumeRef.setAttribute(PAGE_ID_ATTRIBUTE, pageId);
				Object pageNumber = bibRefs[r].annotation.getAttribute(PAGE_NUMBER_ATTRIBUTE);
				if (pageNumber != null)
					volumeRef.setAttribute(PAGE_NUMBER_ATTRIBUTE, pageNumber);
				
				bibRefs[r].volumeRef = new BibRef(volumeRef);
				bibRefs[r].volumeRef.parentRef = bibRefs[r];
				volumeRefList.add(bibRefs[r].volumeRef);
			}
		}
		
		if (volumeRefList.size() == 0)
			return;
		
		BibRef[] volumeRefs = ((BibRef[]) volumeRefList.toArray(new BibRef[volumeRefList.size()]));
		this.parseBibRefs(volumeRefs, authorListStyle, bibRefStyle, pm);
		
		for (int r = 0; r < bibRefs.length; r++) {
			if (bibRefs[r].volumeRef == null)
				continue;
			
			//	transfer editors
			if (bibRefs[r].volumeRef.authors != null) {
				bibRefs[r].editors = new Annotation[bibRefs[r].volumeRef.authors.length];
				for (int a = 0; a < bibRefs[r].volumeRef.authors.length; a++) {
					bibRefs[r].editors[a] = Gamta.newAnnotation(bibRefs[r].annotation, EDITOR_ANNOTATION_TYPE, (bibRefs[r].volumeRef.annotation.getStartIndex() + bibRefs[r].volumeRef.authors[a].getStartIndex()), bibRefs[r].volumeRef.authors[a].size());
					bibRefs[r].editors[a].copyAttributes(bibRefs[r].volumeRef.authors[a]);
				}
			}
			
			//	transfer volume designators ...
			if (bibRefs[r].volumeRef.volumeDesignators != null) {
				bibRefs[r].volumeDesignators = new Annotation[bibRefs[r].volumeRef.volumeDesignators.length];
				for (int v = 0; v < bibRefs[r].volumeRef.volumeDesignators.length; v++) {
					bibRefs[r].volumeDesignators[v] = Gamta.newAnnotation(bibRefs[r].annotation, PART_DESIGNATOR_ANNOTATION_TYPE, (bibRefs[r].volumeRef.annotation.getStartIndex() + bibRefs[r].volumeRef.volumeDesignators[v].getStartIndex()), bibRefs[r].volumeRef.volumeDesignators[v].size());
					bibRefs[r].volumeDesignators[v].setAttribute(TYPE_ATTRIBUTE, VOLUME_DESIGNATOR_TYPE);
				}
			}
			if (bibRefs[r].volumeRef.volumeDesignator != null) {
				bibRefs[r].volumeDesignator = Gamta.newAnnotation(bibRefs[r].annotation, PART_DESIGNATOR_ANNOTATION_TYPE, (bibRefs[r].volumeRef.annotation.getStartIndex() + bibRefs[r].volumeRef.volumeDesignator.getStartIndex()), bibRefs[r].volumeRef.volumeDesignator.size());
				bibRefs[r].volumeDesignator.setAttribute(TYPE_ATTRIBUTE, VOLUME_DESIGNATOR_TYPE);
			}
			
			//	... issue designators ...
			if (bibRefs[r].volumeRef.issueDesignators != null) {
				bibRefs[r].issueDesignators = new Annotation[bibRefs[r].volumeRef.issueDesignators.length];
				for (int i = 0; i < bibRefs[r].volumeRef.issueDesignators.length; i++) {
					bibRefs[r].issueDesignators[i] = Gamta.newAnnotation(bibRefs[r].annotation, PART_DESIGNATOR_ANNOTATION_TYPE, (bibRefs[r].volumeRef.annotation.getStartIndex() + bibRefs[r].volumeRef.issueDesignators[i].getStartIndex()), bibRefs[r].volumeRef.issueDesignators[i].size());
					bibRefs[r].issueDesignators[i].setAttribute(TYPE_ATTRIBUTE, ISSUE_DESIGNATOR_TYPE);
				}
			}
			if (bibRefs[r].volumeRef.issueDesignator != null) {
				bibRefs[r].issueDesignator = Gamta.newAnnotation(bibRefs[r].annotation, PART_DESIGNATOR_ANNOTATION_TYPE, (bibRefs[r].volumeRef.annotation.getStartIndex() + bibRefs[r].volumeRef.issueDesignator.getStartIndex()), bibRefs[r].volumeRef.issueDesignator.size());
				bibRefs[r].issueDesignator.setAttribute(TYPE_ATTRIBUTE, ISSUE_DESIGNATOR_TYPE);
			}
			
			//	... and number designators
			if (bibRefs[r].volumeRef.numberDesignators != null) {
				bibRefs[r].numberDesignators = new Annotation[bibRefs[r].volumeRef.numberDesignators.length];
				for (int i = 0; i < bibRefs[r].volumeRef.numberDesignators.length; i++) {
					bibRefs[r].numberDesignators[i] = Gamta.newAnnotation(bibRefs[r].annotation, PART_DESIGNATOR_ANNOTATION_TYPE, (bibRefs[r].volumeRef.annotation.getStartIndex() + bibRefs[r].volumeRef.numberDesignators[i].getStartIndex()), bibRefs[r].volumeRef.numberDesignators[i].size());
					bibRefs[r].numberDesignators[i].setAttribute(TYPE_ATTRIBUTE, NUMBER_DESIGNATOR_TYPE);
				}
			}
			if (bibRefs[r].volumeRef.numberDesignator != null) {
				bibRefs[r].numberDesignator = Gamta.newAnnotation(bibRefs[r].annotation, PART_DESIGNATOR_ANNOTATION_TYPE, (bibRefs[r].volumeRef.annotation.getStartIndex() + bibRefs[r].volumeRef.numberDesignator.getStartIndex()), bibRefs[r].volumeRef.numberDesignator.size());
				bibRefs[r].numberDesignator.setAttribute(TYPE_ATTRIBUTE, NUMBER_DESIGNATOR_TYPE);
			}
			
			//	transfer structural details
			for (int s = 0; s < bibRefs[r].volumeRef.structure.details.length; s++) {
				if (AUTHOR_LIST_ANNOTATION_TYPE.equals(bibRefs[r].volumeRef.structure.details[s]))
					bibRefs[r].structure.details[s + bibRefs[r].volumeRef.annotation.getStartIndex()] = EDITOR_LIST_ANNOTATION_TYPE;
				else bibRefs[r].structure.details[s + bibRefs[r].volumeRef.annotation.getStartIndex()] = bibRefs[r].volumeRef.structure.details[s];
			}
		}
	}
	
	private void getBaseDetails(BibRef bibRef, NameStyle nameStyle) {
		if (DEBUG) System.out.println("Parsing bibliographic reference " + bibRef.annotation.toXML());
		
		//	annotate URLs & DOIs (helps filtering numerical attributes)
		bibRef.urls = Gamta.extractAllMatches(bibRef.annotation, urlPattern, false, true, false);
		bibRef.dois = Gamta.extractAllMatches(bibRef.annotation, doiPattern, false, true, false);
		if ((bibRef.urls.length + bibRef.dois.length) != 0) {
			if (DEBUG) System.out.println(" - URLs/DOIs:");
			for (int u = 0; u < bibRef.urls.length; u++) {
				bibRef.urls[u] = this.trimUrlOrDoi(bibRef, bibRef.urls[u], false);
				if (DEBUG) System.out.println("   - URL: " + bibRef.urls[u].getValue());
			}
			for (int d = 0; d < bibRef.dois.length; d++) {
				bibRef.dois[d] = this.trimUrlOrDoi(bibRef, bibRef.dois[d], false);
				if (DEBUG) System.out.println("   - DOI: " + bibRef.dois[d].getValue());
			}
		}
		
		//	this one's been parsed before, use existing annotations
		if (bibRef.preExistingStructure) {
			if (DEBUG) System.out.println(" ==> done with pre-existing structure");
			
			//	- year (four digit number between 1500 and 2100)
			bibRef.years = bibRef.annotation.getAnnotations(YEAR_ANNOTATION_TYPE);
			
			//	- author names (try "Initials LastName", "LastName, Initials", "FirstName LastName", and "LastName, FirstName", then choose the pattern with most matches; if no match found in some reference(s), try "LastName" as well)
			bibRef.authorNames = bibRef.annotation.getAnnotations(AUTHOR_ANNOTATION_TYPE);
			
			//	- page ranges ("pp." or "pages" followed by "Number - Number", or "p." or "page" followed by a number)
			bibRef.pageRanges = bibRef.annotation.getAnnotations(PAGINATION_ANNOTATION_TYPE);
			
			//	- page numbers ("p." or "page" followed by a number)
			bibRef.pageNumbers = new Annotation[0];
			
			//	- volume/issue numbers ("no.", "vol.", etc. followed by a number)
			bibRef.partDesignators = bibRef.annotation.getAnnotations(PART_DESIGNATOR_ANNOTATION_TYPE);
			
			//	- URL access dates ("accessed <day> <month> <year>")
			bibRef.labeledDates = new Annotation[0];
			Annotation[] aDates = bibRef.annotation.getAnnotations(ACCESS_DATE_ANNOTATION_TYPE);
			if (aDates.length != 0)
				bibRef.urlAccessDate = aDates[0];
			
			//	classify part designators
			this.classifyPartDesignators(bibRef, false);
			
			//	... and we're done here
			return;
		}
		
		//	get labeled dates (URL access dates, publication dates, etc.)
		bibRef.labeledDates = this.getLabeledDates(bibRef.annotation);
		if (DEBUG) System.out.println(" - labeled dates: " + Arrays.toString(bibRef.labeledDates));
		
		//	create initial filters from highly secure matches
		boolean[] labeledDateFilter = createTokenFilter(bibRef.annotation, bibRef.labeledDates);
		boolean[] urlDoiFilter = createTokenFilter(bibRef.annotation, bibRef.urls);
		augmentFilteredTokens(urlDoiFilter, bibRef.dois, null);
		
		//	get URLs and DOIs split up by spaces (mostly resulting from line wrapping)
		this.getBrokenURLsAndDOIs(bibRef, labeledDateFilter, urlDoiFilter);
		
		//	- year (four digit number between 1500 and 2100)
		if (bibRef.parentRef != null) {
			bibRef.years = new Annotation[0];
			if (DEBUG) System.out.println(" - years: " + Arrays.toString(bibRef.years));
		}
		else {
			bibRef.years = this.getYears(bibRef, urlDoiFilter, true);
			if (DEBUG) System.out.println(" - years: " + Arrays.toString(bibRef.years));
			if (bibRef.years.length == 0) {
				bibRef.years = this.getYears(bibRef, urlDoiFilter, false);
				if (DEBUG) System.out.println(" - all years: " + Arrays.toString(bibRef.years));
			}
		}
		
		//	- author names (try "Initials LastName", "LastName, Initials", "FirstName LastName", and "LastName, FirstName", then choose the pattern with most matches; if no match found in some reference(s), try "LastName" as well)
		bibRef.authorNames = this.getAuthorNames(bibRef.annotation, bibRef.titleNumberToken, nameStyle);
		if (DEBUG) System.out.println(" - author names: " + Arrays.toString(bibRef.authorNames));
		
		//	- editor list labels
		if (bibRef.parentRef != null) {
			bibRef.editorListLabels = Gamta.extractAllMatches(bibRef.annotation, this.editorListLabelRegEx);
			if (DEBUG) System.out.println(" - editor list labels: " + Arrays.toString(bibRef.editorListLabels));
		}
		
		//	- page ranges ("pp." or "pages" followed by "Number - Number", or "p." or "page" followed by a number)
		bibRef.pageRanges = ((bibRef.parentRef != null) ? new Annotation[0] : this.getPageRanges(bibRef, urlDoiFilter));
		if (DEBUG) System.out.println(" - page ranges: " + Arrays.toString(bibRef.pageRanges));
		
		//	- page numbers ("p." or "page" followed by a number)
		bibRef.pageNumbers = ((bibRef.parentRef != null) ? new Annotation[0] : this.getPageNumbers(bibRef, urlDoiFilter));
		if (DEBUG) System.out.println(" - page numbers: " + Arrays.toString(bibRef.pageNumbers));
		
		//	- volume/issue numbers ("no.", "vol.", etc. followed by a number)
		bibRef.partDesignators = (((bibRef.parentRef != null) && (bibRef.parentRef.numberDetailBlock != null)) ? new Annotation[0] : this.getPartDesignators(bibRef, urlDoiFilter));
		if (DEBUG) System.out.println(" - part designators: " + Arrays.toString(bibRef.partDesignators));
		
		//	forget about page numbers and part designators if there are book content infos and no page ranges (if page range present along with part designators, we have a rare mixture ...)
		if ((bibRef.bookContentInfos.size() != 0) && (bibRef.pageRanges.length == 0)) {
			bibRef.pageNumbers = new Annotation[0];
			bibRef.partDesignators = new Annotation[0];
		}
		
		//	use labeled dates for filtering years, page numbers, and part designators
		if (bibRef.labeledDates.length != 0) {
			bibRef.years = filterContained(bibRef.years, labeledDateFilter, true);
			if (DEBUG) System.out.println("   - years filtered to: " + Arrays.toString(bibRef.years));
			bibRef.pageNumbers = filterContained(bibRef.pageNumbers, labeledDateFilter, true);
			if (DEBUG) System.out.println("   - page numbers filtered to: " + Arrays.toString(bibRef.pageNumbers));
			bibRef.partDesignators = filterContained(bibRef.partDesignators, labeledDateFilter, true);
			if (DEBUG) System.out.println("   - part designators filtered to: " + Arrays.toString(bibRef.partDesignators));
		}
		
		//	get dates in general (also part of title, etc.)
		Annotation[] dates = this.getDates(bibRef.annotation);
		if (DEBUG) System.out.println(" - dates: " + Arrays.toString(dates));
		
		//	use dates for filtering years, page numbers, and part designators
		if (dates.length != 0) {
			boolean[] dateFilter = createTokenFilter(bibRef.annotation, dates);
			bibRef.years = filterContained(bibRef.years, dateFilter, true);
			if (DEBUG) System.out.println("   - years filtered to: " + Arrays.toString(bibRef.years));
			bibRef.pageNumbers = filterContained(bibRef.pageNumbers, dateFilter, true);
			if (DEBUG) System.out.println("   - page numbers filtered to: " + Arrays.toString(bibRef.pageNumbers));
			bibRef.partDesignators = filterContained(bibRef.partDesignators, dateFilter, true);
			if (DEBUG) System.out.println("   - part designators filtered to: " + Arrays.toString(bibRef.partDesignators));
		}
		
		//	get part designator and pagination blocks ("<volume> (<issue>) ':' <pagination>"), optionally also including year
		bibRef.numberDetailBlocks = this.getNumberDetailBlocks(bibRef);
		if (DEBUG) {
			for (int b = 0; b < bibRef.numberDetailBlocks.length; b++)
				System.out.println(" - number detail block: " + bibRef.numberDetailBlocks[b].toXML());
		}
		
		//	get URL access date if non-DOI URL present
		if (bibRef.urls.length > bibRef.dois.length) {
			if ((bibRef.labeledDates.length != 0) && (bibRef.labeledDates[bibRef.labeledDates.length-1].getStartIndex() >= bibRef.urls[0].getEndIndex())) {
				for (int d = 0; d < dates.length; d++)
					if (AnnotationUtils.liesIn(dates[d], bibRef.labeledDates[bibRef.labeledDates.length-1])) {
						bibRef.urlAccessDate = dates[d];
						if (DEBUG) System.out.println("   - URL access date: " + bibRef.urlAccessDate.toXML());
						break;
					}
			}
			else if ((dates.length != 0) && (dates[dates.length-1].getStartIndex() >= bibRef.urls[0].getEndIndex())) {
				bibRef.urlAccessDate = dates[dates.length-1];
				if (DEBUG) System.out.println("   - URL access date: " + bibRef.urlAccessDate.toXML());
			}
		}
	}
	
	private void getBrokenURLsAndDOIs(BibRef bibRef, boolean[] labeledDateFilter, boolean[] urlDoiFilter) {
		Annotation[] urlStarts = Gamta.extractAllMatches(bibRef.annotation, urlStartPattern, false, true, false);
		if (urlStarts.length == 0)
			return;
		AnnotationIndex urlPartIndex = new AnnotationIndex();
		
		//	index URL starts (trim where required)
		for (int s = 0; s < urlStarts.length; s++) {
			urlStarts[s] = this.trimUrlOrDoi(bibRef, urlStarts[s], true);
			if (urlStarts[s] == null)
				continue;
			//	TODO any further filters for fragments? by minimum size? by token diversity? against negative patterns?
			urlPartIndex.addAnnotation(urlStarts[s], "start");
		}
		if (DEBUG) System.out.println(" - URL starts: " + Arrays.toString(urlStarts));
		
		//	add fragments (trim where required)
		Annotation[] urlFragments = Gamta.extractAllMatches(bibRef.annotation, urlFragmentPattern, false, true, false);
		if (DEBUG) System.out.println(" - URL fragments: " + Arrays.toString(urlFragments));
		urlFragments = filterOverlapping(urlFragments, labeledDateFilter, true);
		if (DEBUG) System.out.println(" - URL fragments filtered to: " + Arrays.toString(urlFragments));
		for (int f = 0; f < urlFragments.length; f++) {
			urlFragments[f] = this.trimUrlOrDoi(bibRef, urlFragments[f], true);
			if (urlFragments[f] == null)
				continue;
			if (Gamta.isOpeningBracket(urlFragments[f].firstValue())) {
				if (urlFragments[f].size() < 3)
					continue; // most likely start of a remark in brackets
				if ((urlFragments[f].size() < 4) && Gamta.closes(urlFragments[f].lastValue(), urlFragments[f].firstValue()))
					continue; // most likely single-word remark in brackets
				if ((2 < urlFragments[f].size()) && (urlFragments[f].size() < 5) && (".".equals(urlFragments[f].lastValue()) || ",".equals(urlFragments[f].lastValue())) && Gamta.closes(urlFragments[f].valueAt(urlFragments[f].size()-2), urlFragments[f].firstValue()))
					continue; // most likely single-word remark in brackets followed by dot or comma
			}
			//	TODO any further filters for fragments? by minimum size? by token diversity? against negative patterns?
			urlPartIndex.addAnnotation(urlFragments[f], "fragment");
		}
		
		//	get restored URLs
		Annotation[] urls = AnnotationPatternMatcher.getMatches(bibRef.annotation, urlPartIndex, "<start> <fragment>+");
		if (urls.length == 0)
			return;
		
		//	classify restored URLs
		if (DEBUG) System.out.println(" - restored broken URLs:");
		ArrayList rUrls = new ArrayList();
		ArrayList rDois = new ArrayList();
		for (int u = 0; u < urls.length; u++) {
			urls[u] = this.trimUrlOrDoi(bibRef, urls[u], false);
			if (urls[u] == null)
				continue;
			if (DEBUG) System.out.println("   - " + urls[u].getValue());
			String rUrl = urls[u].getValue().replaceAll("\\s+", "");
			if (rUrl.matches(urlPattern)) {
				rUrls.add(urls[u]);
				if (DEBUG) System.out.println("     ==> URL");
			}
			if (rUrl.matches(doiPattern)) {
				rDois.add(urls[u]);
				if (DEBUG) System.out.println("     ==> DOI");
			}
		}
		
		//	filter sub URLs and sub DOIs (we might have restored from three or more parts)
		for (int u = 1; u < rUrls.size(); u++) {
			if (AnnotationUtils.contains(((Annotation) rUrls.get(u-1)), ((Annotation) rUrls.get(u))))
				rUrls.remove(u--);
		}
		for (int d = 1; d < rDois.size(); d++) {
			if (AnnotationUtils.contains(((Annotation) rDois.get(d-1)), ((Annotation) rDois.get(d))))
				rDois.remove(d--);
		}
		
		//	replace previous URLs and DOIs, and augment filter
		if (bibRef.urls.length <= rUrls.size()) {
			bibRef.urls = ((Annotation[]) rUrls.toArray(new Annotation[rUrls.size()]));
			augmentFilteredTokens(urlDoiFilter, bibRef.urls, null); 
		}
		if (bibRef.dois.length <= rDois.size()) {
			bibRef.dois = ((Annotation[]) rDois.toArray(new Annotation[rDois.size()]));
			augmentFilteredTokens(urlDoiFilter, bibRef.dois, null); 
		}
		
		//	what do we have?
		if (DEBUG && ((bibRef.urls.length + bibRef.dois.length) != 0)) {
			System.out.println("Restored URLs/DOIs in " + bibRef.annotation.getValue());
			for (int u = 0; u < bibRef.urls.length; u++)
				System.out.println("  URL: " + bibRef.urls[u].getValue());
			for (int d = 0; d < bibRef.dois.length; d++)
				System.out.println("  DOI: " + bibRef.dois[d].getValue());
		}
	}
	
	private Annotation trimUrlOrDoi(BibRef bibRef, Annotation urlOrDoi, boolean isFragment) {
		if ((isFragment ? ",;" : ",;.:([{").indexOf(urlOrDoi.lastValue()) == -1)
			return urlOrDoi;
		if (urlOrDoi.size() == 1)
			return null;
		Annotation tUrlOrDoi = Gamta.newAnnotation(bibRef.annotation, urlOrDoi.getType(), urlOrDoi.getStartIndex(), (urlOrDoi.size() - 1));
		tUrlOrDoi.copyAttributes(urlOrDoi);
		return tUrlOrDoi;
	}
	
	private static boolean[] createTokenFilter(Annotation base, Annotation[] annots) {
		boolean[] tokenFiltered = new boolean[base.size()];
		Arrays.fill(tokenFiltered, false);
		if (annots != null)
			augmentFilteredTokens(tokenFiltered, annots, null);
		return tokenFiltered;
	}
	
	private static void augmentFilteredTokens(boolean[] tokenFiltered, Annotation annot, String annotLabel) {
		Arrays.fill(tokenFiltered, annot.getStartIndex(), annot.getEndIndex(), true);
		if (DEBUG && (annotLabel != null)) System.out.println(" - excluding " + annotLabel + " '" + annot.getValue() + "'");
	}
	
	private static void augmentFilteredTokens(boolean[] tokenFiltered, Annotation[] annots, String annotLabel) {
		for (int a = 0; a < annots.length; a++) {
			Arrays.fill(tokenFiltered, annots[a].getStartIndex(), annots[a].getEndIndex(), true);
			if (DEBUG && (annotLabel != null)) System.out.println(" - excluding " + annotLabel + " '" + annots[a].getValue() + "'");
		}
	}
	
	private static int countFilteredTokens(Annotation annot, boolean[] tokenFiltered) {
		int filteredTokens = 0;
		for (int t = annot.getStartIndex(); t < annot.getEndIndex(); t++) {
			if (tokenFiltered[t])
				filteredTokens++;
		}
		return filteredTokens;
	}
	
	private static Annotation[] filterContained(Annotation[] annots, boolean[] tokenFiltered, boolean allowEmptyResult) {
		if ((annots == null) || (annots.length == 0))
			return annots; // nothing to filter out
		ArrayList nonContained = new ArrayList();
		for (int a = 0; a < annots.length; a++) {
			if (annots[a] == null)
				continue;
			int filteredTokens = countFilteredTokens(annots[a], tokenFiltered);
			if (filteredTokens < annots[a].size())
				nonContained.add(annots[a]);
		}
		return assessFilterResult(annots, nonContained, allowEmptyResult);
	}
	
	private static Annotation[] filterNonContained(Annotation[] annots, boolean[] tokenFiltered, boolean allowEmptyResult) {
		if ((annots == null) || (annots.length == 0))
			return annots; // nothing to filter out
		ArrayList contained = new ArrayList();
		for (int a = 0; a < annots.length; a++) {
			if (annots[a] == null)
				continue;
			int filteredTokens = countFilteredTokens(annots[a], tokenFiltered);
			if (filteredTokens == annots[a].size())
				contained.add(annots[a]);
		}
		return assessFilterResult(annots, contained, allowEmptyResult);
	}
	
	private static Annotation[] filterOverlapping(Annotation[] annots, boolean[] tokenFiltered, boolean allowEmptyResult) {
		if ((annots == null) || (annots.length == 0))
			return annots; // nothing to filter out
		ArrayList disjoint = new ArrayList();
		for (int a = 0; a < annots.length; a++) {
			if (annots[a] == null)
				continue;
			int filteredTokens = countFilteredTokens(annots[a], tokenFiltered);
			if (filteredTokens == 0)
				disjoint.add(annots[a]);
		}
		return assessFilterResult(annots, disjoint, allowEmptyResult);
	}
	
	private static Annotation[] filterDisjoint(Annotation[] annots, boolean[] tokenFiltered, boolean allowEmptyResult) {
		if ((annots == null) || (annots.length == 0))
			return annots; // nothing to filter out
		ArrayList overlapping = new ArrayList();
		for (int a = 0; a < annots.length; a++) {
			if (annots[a] == null)
				continue;
			int filteredTokens = countFilteredTokens(annots[a], tokenFiltered);
			if (filteredTokens != 0)
				overlapping.add(annots[a]);
		}
		return assessFilterResult(annots, overlapping, allowEmptyResult);
	}
	
	private static Annotation[] assessFilterResult(Annotation[] annots, ArrayList filteredAnnots, boolean allowEmptyResult) {
		if (filteredAnnots.size() == annots.length)
			return annots; // nothing filtered out
		if (allowEmptyResult || (filteredAnnots.size() != 0))
			return ((Annotation[]) filteredAnnots.toArray(new Annotation[filteredAnnots.size()])); // filtered result OK
		return annots; // hold on to what we got if empty result forbidden
	}
	
	private void getStructures(BibRef bibRef) {
		
		//	wrap author lists (avoid labeled editor lists in main references, and prefer them in volume references)
		Annotation[] authorLists;
		if (bibRef.preExistingStructure) {
			authorLists = new Annotation[1];
			authorLists[0] = bibRef.authorList;
		}
		else {
			ArrayList plainAuthorLists = new ArrayList();
			ArrayList labeledEditorAuthorLists = new ArrayList();
			for (int l = 0; l < bibRef.authorLists.length; l++) {
				if (bibRef.authorLists[l].editorListLabel == null)
					plainAuthorLists.add(bibRef.authorLists[l].annotation);
				else labeledEditorAuthorLists.add(bibRef.authorLists[l].annotation);
			}
			if (bibRef.parentRef == null) {
				if (plainAuthorLists.isEmpty())
					authorLists = ((Annotation[]) labeledEditorAuthorLists.toArray(new Annotation[labeledEditorAuthorLists.size()]));
				else authorLists = ((Annotation[]) plainAuthorLists.toArray(new Annotation[plainAuthorLists.size()]));
			}
			else {
				if (labeledEditorAuthorLists.isEmpty())
					authorLists = ((Annotation[]) plainAuthorLists.toArray(new Annotation[plainAuthorLists.size()]));
				else authorLists = ((Annotation[]) labeledEditorAuthorLists.toArray(new Annotation[labeledEditorAuthorLists.size()]));
			}
		}
		
		//	check for labeled editor lists
		boolean gotLabeledEditorList = ((bibRef.parentRef != null) && (bibRef.authorLists.length != 0) && (bibRef.authorLists[0].editorListLabel != null));
		
		//	use only one of page numbers and page ranges for structure generation (prefer page ranges)
		Annotation[] pageIndicators;
		
		//	got a page range
		if (bibRef.pageRanges.length != 0)
			pageIndicators = bibRef.pageRanges;
		
		//	got a secure page number
		else pageIndicators = bibRef.pageNumbers;
		
		//	TODO_ne figure out if this is (a) more helpful, e.g. in references to single pages, or (b) more harmful with numbers in references to whole books
		//	==> seems so, at least with URL filter for numbers
		//	unify page indicators
		for (int i = 0; i < pageIndicators.length; i++) {
			pageIndicators[i].changeTypeTo(PAGINATION_ANNOTATION_TYPE);
			pageIndicators[i].setAttribute("type", ((bibRef.pageRanges.length == 0) ? "pageNumber" : "pageRange"));
		}
		
		//	prepare bridging part designator hints
		Annotation[] partDesignators = new Annotation[bibRef.partDesignators.length];
		for (int p = 0; p < bibRef.partDesignators.length; p++) {
			Annotation partDesignatorHint = ((Annotation) bibRef.partDesignatorHints.get(new Integer(bibRef.partDesignators[p].getStartIndex())));
			if (partDesignatorHint == null)
				partDesignators[p] = bibRef.partDesignators[p];
			else partDesignators[p] = Gamta.newAnnotation(bibRef.annotation, PART_DESIGNATOR_ANNOTATION_TYPE, partDesignatorHint.getStartIndex(), (partDesignatorHint.size() + bibRef.partDesignators[p].size()));
		}
		
		//	generate part designator blocks
		ArrayList partDesignatorBlocks = new ArrayList();
		for (int pdbStart = 0; pdbStart < partDesignators.length; pdbStart++) {
			int pdbEnd = pdbStart;
			
			//	find maximum cohesive block
			for (int l = pdbStart; l < partDesignators.length; l++) {
				
				//	last part designator, has to be block end
				if ((l+1) == partDesignators.length) {
					pdbEnd = l;
					break;
				}
				
				//	next part designator adjacent, block continues
				if (partDesignators[l].getEndIndex() == partDesignators[l+1].getStartIndex())
					continue;
					
				
				//	bridgeable gap to next part designator, block continues
				if (((partDesignators[l].getEndIndex()+1) == partDesignators[l+1].getStartIndex()) && ((bibRef.numberDetailBlock != null) || this.partDesignatorBlockSeparators.contains(bibRef.annotation.valueAt(partDesignators[l].getEndIndex()))))
					continue;
				
				//	end of block reached
				pdbEnd = l;
				break;
			}
			
			//	add all possible blocks within current maximum block
			for (int s = pdbStart; s <= pdbEnd; s++) {
				if ((partDesignators[s].size() > 1) || Gamta.isNumber(partDesignators[s].firstValue()) || (bibRef.numberDetailBlock != null)) // ignore single Roman numbers (all too frequent in the middle of old book titles) unless backed by number detail block
					partDesignatorBlocks.add(partDesignators[s]);
				for (int e = (s+1); e <= pdbEnd; e++)
					partDesignatorBlocks.add(Gamta.newAnnotation(bibRef.annotation, PART_DESIGNATOR_ANNOTATION_TYPE, partDesignators[s].getStartIndex(), (partDesignators[e].getEndIndex() - partDesignators[s].getStartIndex())));
			}
			
			//	start over with next unvisited part designator
			pdbStart = pdbEnd;
		}
		
		//	include preceding and following brackets if respective matching bracket included in block
		for (int p = 0; p < partDesignatorBlocks.size(); p++) {
			Annotation partDesignatorBlock = ((Annotation) partDesignatorBlocks.get(p));
			if (partDesignatorBlock.size() == 1)
				continue;
			
			String bracket = null;
			for (int t = 0; t < partDesignatorBlock.size(); t++)
				if (Gamta.isBracket(partDesignatorBlock.valueAt(t))) {
					bracket = partDesignatorBlock.valueAt(t);
					break;
				}
			if (bracket == null)
				continue;
			
			if (Gamta.isOpeningBracket(bracket) && (partDesignatorBlock.getEndIndex() < bibRef.annotation.size()) && Gamta.closes(bibRef.annotation.valueAt(partDesignatorBlock.getEndIndex()), bracket))
				partDesignatorBlock = Gamta.newAnnotation(bibRef.annotation, PART_DESIGNATOR_ANNOTATION_TYPE, partDesignatorBlock.getStartIndex(), (partDesignatorBlock.size() + 1));
			else if (Gamta.isClosingBracket(bracket) && (partDesignatorBlock.getStartIndex() != 0) && Gamta.opens(bibRef.annotation.valueAt(partDesignatorBlock.getStartIndex()-1), bracket))
				partDesignatorBlock = Gamta.newAnnotation(bibRef.annotation, PART_DESIGNATOR_ANNOTATION_TYPE, (partDesignatorBlock.getStartIndex()-1), (partDesignatorBlock.size() + 1));
			
			if (partDesignatorBlock != partDesignatorBlocks.get(p))
				partDesignatorBlocks.set(p, partDesignatorBlock);
		}
		
		//	sort part designator blocks so larger ones are preferred in structure vote
		Collections.sort(partDesignatorBlocks);
		
		//	retain only main part designator block if we have a solid block of number details
		if ((bibRef.numberDetailBlock != null) && (partDesignatorBlocks.size() > 1))
			for (int p = 0; p < partDesignatorBlocks.size(); p++) {
				Annotation pdb = ((Annotation) partDesignatorBlocks.get(p));
				for (int cp = (p+1); cp < partDesignatorBlocks.size(); cp++) {
					Annotation cPdb = ((Annotation) partDesignatorBlocks.get(cp));
					if (AnnotationUtils.liesIn(cPdb, pdb))
						partDesignatorBlocks.remove(cp--);
					else if (pdb.getEndIndex() <= cPdb.getStartIndex())
						break;
				}
			}
		
		//	report
		if (DEBUG) {
			System.out.println("Part designator blocks in " + bibRef.annotation.toXML());
			for (int p = 0; p < partDesignatorBlocks.size(); p++)
				System.out.println(((Annotation) partDesignatorBlocks.get(p)).toXML());
		}
		
		//	TODO consider creating blocks out of adjacent years that differ by one
		
		//	set up structure relevant details
		String[] workingStructure = new String[bibRef.annotation.size()];
		Annotation[][] details = {
				authorLists,
				bibRef.years,
				pageIndicators,
				((Annotation[]) partDesignatorBlocks.toArray(new Annotation[partDesignatorBlocks.size()])),
		};
		boolean[] tryWithoutIfGiven = {
				(!bibRef.preExistingStructure && !gotLabeledEditorList),
				false,
				(!bibRef.preExistingStructure && (bibRef.numberDetailBlock == null) && ((pageIndicators.length != 1) || !pageIndicators[0].hasAttribute("labeled"))),
				(!bibRef.preExistingStructure && (bibRef.numberDetailBlock == null)),
			};
		
		//	get structures
		this.getStructures(bibRef, details, 0, tryWithoutIfGiven, workingStructure);
	}
	
	private void getStructures(BibRef bibRef, Annotation[][] details, int detailTypeIndex, boolean[] tryWithoutIfGiven, String[] workingStructure) {
		
		//	we're done here
		if (detailTypeIndex == details.length) {
			bibRef.structures.add(new Structure(bibRef.annotation, workingStructure));
			return;
		}
		
		//	try all options for current detail type
		for (int d = 0; d < details[detailTypeIndex].length; d++) {
			if (details[detailTypeIndex][d] == null)
				continue;
			
			//	check if current detail fits
			boolean fits = true;
			for (int s = details[detailTypeIndex][d].getStartIndex(); s < details[detailTypeIndex][d].getEndIndex(); s++)
				fits = (fits && (workingStructure[s] == null));
			
			//	it fits
			if (fits) {
				
				//	put current detail
				for (int s = details[detailTypeIndex][d].getStartIndex(); s < details[detailTypeIndex][d].getEndIndex(); s++)
					workingStructure[s] = details[detailTypeIndex][d].getType();
				
				//	proceed with current detail
				this.getStructures(bibRef, details, (detailTypeIndex+1), tryWithoutIfGiven, workingStructure);
				
				//	clean up
				for (int s = details[detailTypeIndex][d].getStartIndex(); s < details[detailTypeIndex][d].getEndIndex(); s++)
					workingStructure[s] = null;
			}
		}
		
		//	also try proceeding without current detail type (allows for trying out more at the same time)
		if ((details[detailTypeIndex].length == 0) || tryWithoutIfGiven[detailTypeIndex])
			this.getStructures(bibRef, details, (detailTypeIndex+1), tryWithoutIfGiven, workingStructure);
	}
	
	private void indexStructures(BibRef bibRef, CountingSet structureCounts, HashMap punctSummaryElementSets, HashMap summaryElementSets, HashMap typeElementSets) {
		
		//	set up auxiliary data structures
		StringVector typeStrings = new StringVector();
		StringVector summaryStrings = new StringVector();
		StringVector punctSummaryStrings = new StringVector();
		
		//	count structures
		if (DEBUG) System.out.println(bibRef.annotation.toXML());
		for (int s = 0; s < bibRef.structures.size(); s++) {
			Structure structure = ((Structure) bibRef.structures.get(s));
			if (structure.detailTypes.contains(PAGE_NUMBER_TYPE) && structure.detailTypes.contains(PAGE_RANGE_ANNOTATION_TYPE)) {
				bibRef.structures.remove(s--);
				continue;
			}
			
			typeStrings.addElementIgnoreDuplicates(structure.typeString);
			if (!typeElementSets.containsKey(structure.typeString))
				typeElementSets.put(structure.typeString, new LinkedHashSet(Arrays.asList(structure.types)));
			
			summaryStrings.addElementIgnoreDuplicates(structure.summaryString);
			if (!summaryElementSets.containsKey(structure.summaryString))
				summaryElementSets.put(structure.summaryString, new LinkedHashSet(Arrays.asList(structure.summary)));
			
			punctSummaryStrings.addElementIgnoreDuplicates(structure.punctSummaryString);
			if (!punctSummaryElementSets.containsKey(structure.punctSummaryString))
				punctSummaryElementSets.put(structure.punctSummaryString, new LinkedHashSet(Arrays.asList(structure.punctSummary)));
		}
		
		for (int s = 0; s < typeStrings.size(); s++)
			structureCounts.add(typeStrings.get(s));
		for (int s = 0; s < summaryStrings.size(); s++)
			structureCounts.add(summaryStrings.get(s));
		for (int s = 0; s < punctSummaryStrings.size(); s++)
			structureCounts.add(punctSummaryStrings.get(s));
	}
	
//	private void selectStructure(BibRef bibRef, int bibRefCount, StringVector structures, final StringIndex structureCounts, StringVector separators, StringIndex separatorFrequencies, HashMap punctSummaryElementSets, HashMap summaryElementSets, HashMap typeElementSets) {
	private void selectStructure(BibRef bibRef, int bibRefCount, final CountingSet structureCounts, HashMap punctSummaryElementSets, HashMap summaryElementSets, HashMap typeElementSets) {
		if (DEBUG) System.out.println(bibRef.annotation.toXML());
		
		if (false && DEBUG_STRUCTURE_SCORING) {
			Collections.sort(bibRef.structures, new Comparator() {
				public int compare(Object o1, Object o2) {
					Structure s1 = ((Structure) o1);
					Structure s2 = ((Structure) o2);
					return (structureCounts.getCount(s2.punctSummaryString) - structureCounts.getCount(s1.punctSummaryString));
				}
			});
			for (int s = 0; s < bibRef.structures.size(); s++) {
				Structure structure = ((Structure) bibRef.structures.get(s));
				if (DEBUG_STRUCTURE_SCORING) System.out.println("PSS: " + structureCounts.getCount(structure.punctSummaryString) + "/" + bibRefCount + ": " + structure.punctSummaryString);
			}
			
			Collections.sort(bibRef.structures, new Comparator() {
				public int compare(Object o1, Object o2) {
					Structure s1 = ((Structure) o1);
					Structure s2 = ((Structure) o2);
					return (structureCounts.getCount(s2.summaryString) - structureCounts.getCount(s1.summaryString));
				}
			});
			for (int s = 0; s < bibRef.structures.size(); s++) {
				Structure structure = ((Structure) bibRef.structures.get(s));
				if (DEBUG_STRUCTURE_SCORING) System.out.println("SS:  " + structureCounts.getCount(structure.summaryString) + "/" + bibRefCount + ": " + structure.summaryString);
			}
			
			Collections.sort(bibRef.structures, new Comparator() {
				public int compare(Object o1, Object o2) {
					Structure s1 = ((Structure) o1);
					Structure s2 = ((Structure) o2);
					return (structureCounts.getCount(s2.typeString) - structureCounts.getCount(s1.typeString));
				}
			});
			for (int s = 0; s < bibRef.structures.size(); s++) {
				Structure structure = ((Structure) bibRef.structures.get(s));
				if (DEBUG_STRUCTURE_SCORING) System.out.println("TS:  " + structureCounts.getCount(structure.typeString) + "/" + bibRefCount + ": " + structure.typeString);
			}
		}
		
		//	vote structure based on (a) support/frequency and (b) number of detail types covered
		int maxScore = 0;
		Structure maxScoreStructure = null;
		int maxFuzzyScore = 0;
		Structure maxFuzzyScoreStructure = null;
		for (int s = 0; s < bibRef.structures.size(); s++) {
			Structure structure = ((Structure) bibRef.structures.get(s));
			int score = 0;
			
			//	this scoring function seems to work very well !!!
			//	TODOne: experiment with exponents of |detailType| power ==> seems to work very well with square
			int psScore = (((int) Math.pow(structure.detailTypes.size(), 2)) * structureCounts.getCount(structure.punctSummaryString));
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" - " + structure.punctSummaryString + " -PSS-> " + psScore);
			score += psScore;
			
			int sScore = (((int) Math.pow(structure.detailTypes.size(), 2)) * structureCounts.getCount(structure.summaryString));
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" - " + structure.summaryString + " -SS-> " + sScore);
			score += sScore;
			
			int tScore = (((int) Math.pow(structure.detailTypes.size(), 2)) * structureCounts.getCount(structure.typeString));
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" - " + structure.typeString + " -TS-> " + tScore);
			score += tScore;
			
			//	score longes block of '_' (rewards having recognized features close together, thus catch mis-recoginitions in middle of reference)
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" -VB-> " + structure.maxVoidBlockLength);
			score += structure.maxVoidBlockLength;
			
			//	score long author lists (overcomes problems when selecting small sub list of long author list voids long block)
			int authorListLength = 0;
			for (int d = 0; d < structure.details.length; d++) {
				if (AUTHOR_LIST_ANNOTATION_TYPE.equals(structure.details[d]))
					authorListLength++;
			}
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" -AL-> " + authorListLength);
			score += authorListLength;
			
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" =SCORE=> " + score);
			if (score > maxScore) {
				maxScore = score;
				maxScoreStructure = structure;
//				bibRef.structure = structure;
			}
			else if (score == maxScore) {
				
				//	compare order of part designator and page numbers, and length of author list
				int sPageDataIndex = -1;
				int sPartDesIndex = -1;
				int sAuthorListLength = 0;
				for (int d = 0; d < structure.details.length; d++) {
					if ((sPageDataIndex == -1 && PAGINATION_ANNOTATION_TYPE.equals(structure.details[d])))
						sPageDataIndex = d;
					else if ((sPartDesIndex == -1 && PART_DESIGNATOR_ANNOTATION_TYPE.equals(structure.details[d])))
						sPartDesIndex = d;
					else if (AUTHOR_LIST_ANNOTATION_TYPE.equals(structure.details[d]))
						sAuthorListLength++;
				}
				int mssPageDataIndex = -1;
				int mssPartDesIndex = -1;
				int mssAuthorListLength = 0;
				for (int d = 0; d < maxScoreStructure.details.length; d++) {
					if ((mssPageDataIndex == -1 && PAGINATION_ANNOTATION_TYPE.equals(maxScoreStructure.details[d])))
						mssPageDataIndex = d;
					else if ((mssPartDesIndex == -1 && PART_DESIGNATOR_ANNOTATION_TYPE.equals(maxScoreStructure.details[d])))
						mssPartDesIndex = d;
					else if (AUTHOR_LIST_ANNOTATION_TYPE.equals(maxScoreStructure.details[d]))
						mssAuthorListLength++;
				}
				
				//	prefer part designator left of page number
				if ((mssPageDataIndex != -1) && (sPageDataIndex > mssPageDataIndex) && (sPartDesIndex != -1) && (sPartDesIndex < mssPartDesIndex))
					maxScoreStructure = structure;
				
				//	prefer longer author list
				else if (sAuthorListLength > mssAuthorListLength)
					maxScoreStructure = structure;
			}
			
			//	use structure subsumption
			int fuzzyScore = 0;
			
			//	compare punctuated summary
//			System.out.println(" - " + structure.punctSummaryString + " vs.:");
			LinkedHashSet sPunctSummaryElements = ((LinkedHashSet) punctSummaryElementSets.get(structure.punctSummaryString));
			int psFuzzyScore = getFuzzyScore(structure.detailTypes.size(), structure.punctSummaryString, sPunctSummaryElements, structureCounts, punctSummaryElementSets);
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" - " + structure.punctSummaryString + " -PSS-F-> " + psFuzzyScore);
			fuzzyScore += psFuzzyScore;
			
			//	compare summary
//			System.out.println(" - " + structure.summaryString + " vs.:");
			LinkedHashSet sSummaryElements = ((LinkedHashSet) summaryElementSets.get(structure.summaryString));
			int sFuzzyScore = getFuzzyScore(structure.detailTypes.size(), structure.summaryString, sSummaryElements, structureCounts, summaryElementSets);
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" - " + structure.summaryString + " -SS-F-> " + sFuzzyScore);
			fuzzyScore += sFuzzyScore;
			
			//	compare types
//			System.out.println(" - " + structure.typeString + " vs.:");
			LinkedHashSet sTypeElements = ((LinkedHashSet) typeElementSets.get(structure.typeString));
			int tFuzzyScore = getFuzzyScore(structure.detailTypes.size(), structure.typeString, sTypeElements, structureCounts, typeElementSets);
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" - " + structure.typeString + " -TS-F-> " + tFuzzyScore);
			fuzzyScore += tFuzzyScore;
			
			//	score longest block of '_' (rewards having recognized features close together, thus catch mis-recoginitions in middle of reference)
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" -VB-F-> " + structure.maxVoidBlockLength);
			fuzzyScore += structure.maxVoidBlockLength;
			
			//	score number of typed detail tokens (overcomes truncation of multi-part details in favor of void block length)
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" -DT-F-> " + structure.detailTokenCount);
			fuzzyScore += structure.detailTokenCount;
			
			//	score long author lists (overcomes problems when selecting small sub list of long author list voids long block)
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" -AL-F-> " + authorListLength);
			fuzzyScore += authorListLength;
			
			//	got a new leader?
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" =SCORE-F=> " + fuzzyScore);
			if (fuzzyScore > maxFuzzyScore) {
				maxFuzzyScore = fuzzyScore;
				maxFuzzyScoreStructure = structure;
			}
			else if (fuzzyScore == maxFuzzyScore) {
				
				//	compare order or part designator and page numbers
				int sPageDataIndex = -1;
				int sPartDesIndex = -1;
				int sAuthorListLength = 0;
				for (int d = 0; d < structure.details.length; d++) {
					if ((sPageDataIndex == -1 && PAGINATION_ANNOTATION_TYPE.equals(structure.details[d])))
						sPageDataIndex = d;
					else if ((sPartDesIndex == -1 && PART_DESIGNATOR_ANNOTATION_TYPE.equals(structure.details[d])))
						sPartDesIndex = d;
					else if (AUTHOR_LIST_ANNOTATION_TYPE.equals(structure.details[d]))
						sAuthorListLength++;
				}
				int mssPageDataIndex = -1;
				int mssPartDesIndex = -1;
				int mssAuthorListLength = 0;
				for (int d = 0; d < maxFuzzyScoreStructure.details.length; d++) {
					if ((mssPageDataIndex == -1 && PAGINATION_ANNOTATION_TYPE.equals(maxFuzzyScoreStructure.details[d])))
						mssPageDataIndex = d;
					else if ((mssPartDesIndex == -1 && PART_DESIGNATOR_ANNOTATION_TYPE.equals(maxFuzzyScoreStructure.details[d])))
						mssPartDesIndex = d;
					else if (AUTHOR_LIST_ANNOTATION_TYPE.equals(maxFuzzyScoreStructure.details[d]))
						mssAuthorListLength++;
				}
				
				//	prefer part designator left of page number
				if ((mssPageDataIndex != -1) && (sPageDataIndex > mssPageDataIndex) && (sPartDesIndex != -1) && (sPartDesIndex < mssPartDesIndex))
					maxFuzzyScoreStructure = structure;
				
				//	prefer longer author list
				else if (sAuthorListLength > mssAuthorListLength)
					maxFuzzyScoreStructure = structure;
			}
		}
		
		//	assign structure
//		bibRef.structure = maxScoreStructure;
		bibRef.structure = maxFuzzyScoreStructure;
		
		if (bibRef.structure == null) {
			String[] dummyWorkingStructure = new String[bibRef.annotation.size()];
			for (int s = 0; s < dummyWorkingStructure.length; s++)
				dummyWorkingStructure[s] = "_";
			bibRef.structure = new Structure(bibRef.annotation, dummyWorkingStructure);
		}
		
		if (DEBUG) {
			System.out.println(" =plain=> (" + maxScore + ") " + ((maxScoreStructure == null) ? "not found" : maxScoreStructure.punctSummaryString));
			System.out.println(" =fuzzy=> (" + maxFuzzyScore + ") " + ((maxFuzzyScoreStructure == null) ? "not found" : maxFuzzyScoreStructure.punctSummaryString));
			System.out.println("   ==> (" + maxFuzzyScore + ") " + bibRef.structure.punctSummaryString);
		}
		
		//	this one's been parsed before, no annotation to add
		if (bibRef.preExistingStructure)
			return;
		
		//	transform years into annotations (have to do this first so we can get proceedings titles)
		for (int d = 0; d < bibRef.structure.details.length; d++)
			if (YEAR_ANNOTATION_TYPE.equals(bibRef.structure.details[d])) {
				Annotation detail = Gamta.newAnnotation(bibRef.annotation, bibRef.structure.details[d], d, 1);
				if (YEAR_ANNOTATION_TYPE.equals(bibRef.structure.details[d]))
					bibRef.year = detail;
			}
		
		//	get proceedings titles, and remove any part designators they span, also cleaning structure
		Annotation[] proceedingsTitles = this.getProceedingsTitles(bibRef);
		if (proceedingsTitles.length != 0) {
			for (int pt = 0; pt < proceedingsTitles.length; pt++) {
				for (int t = proceedingsTitles[pt].getStartIndex(); t < proceedingsTitles[pt].getEndIndex(); t++)
					bibRef.structure.details[t] = "_";
			}
			bibRef.structure = new Structure(bibRef.annotation, bibRef.structure.details);
		}
		
		//	transform details into annotations
		for (int d = 0; d < bibRef.structure.details.length; d++) {
			if ("_".equals(bibRef.structure.details[d]))
				continue;
			
			int e = (d+1);
			while ((e < bibRef.structure.details.length) && bibRef.structure.details[d].equals(bibRef.structure.details[e]))
				e++;
			Annotation detail = Gamta.newAnnotation(bibRef.annotation, bibRef.structure.details[d], d, (e-d));
			if (AUTHOR_LIST_ANNOTATION_TYPE.equals(bibRef.structure.details[d])) {
				ArrayList authors = null;
				AuthorList authorList = null;
				for (int l = 0; l < bibRef.authorLists.length; l++) {
					if (!AnnotationUtils.equals(detail, bibRef.authorLists[l].annotation, false))
						continue;
					if ((authorList == null) || (bibRef.authorLists[l].bridged.size() < authorList.bridged.size()))
						authorList = bibRef.authorLists[l];
				}
				if (authorList != null) {
					bibRef.authorList = authorList.annotation;
					authors = new ArrayList(authorList.authorNames);
				}
				if (bibRef.authorList == null) {
					bibRef.authorList = detail;
					authors = new ArrayList();
					int authorEnd = -1;
					for (int a = 0; a < bibRef.authorNames.length; a++) {
						if (bibRef.authorNames[a].getStartIndex() <= authorEnd)
							continue;
						if (AnnotationUtils.liesIn(bibRef.authorNames[a], bibRef.authorList)) {
							authors.add(bibRef.authorNames[a]);
							authorEnd = bibRef.authorNames[a].getEndIndex();
						}
					}
				}
				if (authors.size() != 0) {
					Annotation lastAuthor = ((Annotation) authors.get(authors.size() -1));
					if (etAlSpecialType.equals(lastAuthor.getType()))
						authors.remove(authors.size() -1);
				}
				bibRef.authors = ((Annotation[]) authors.toArray(new Annotation[authors.size()]));
			}
			else if (PAGINATION_ANNOTATION_TYPE.equals(bibRef.structure.details[d]) || PAGE_RANGE_ANNOTATION_TYPE.equals(bibRef.structure.details[d]) || PAGE_NUMBER_TYPE.equals(bibRef.structure.details[d])) {
				if (!VOLUME_REFERENCE_ANNOTATION_TYPE.equals(bibRef.annotation.getType()))
					bibRef.pagination = detail;
			}
			else if (PART_DESIGNATOR_ANNOTATION_TYPE.equals(bibRef.structure.details[d])) {
				//	go through part designators and assign respectively
				for (int p = 0; p < bibRef.partDesignators.length; p++) {
					if (!AnnotationUtils.contains(detail, bibRef.partDesignators[p])) {
						System.out.println("Out-of-place part designator: " + bibRef.partDesignators[p].toXML());
						continue;
					}
					String partDesignatorType = ((String) bibRef.partDesignators[p].getAttribute(TYPE_ATTRIBUTE));
					if (VOLUME_DESIGNATOR_TYPE.equals(partDesignatorType))
						bibRef.volumeDesignator = bibRef.partDesignators[p];
					else if (ISSUE_DESIGNATOR_TYPE.equals(partDesignatorType))
						bibRef.issueDesignator = bibRef.partDesignators[p];
					else if (NUMBER_DESIGNATOR_TYPE.equals(partDesignatorType))
						bibRef.numberDesignator = bibRef.partDesignators[p];
					else if (FASCICLE_DESIGNATOR_TYPE.equals(partDesignatorType))
						bibRef.fascicleDesignator = bibRef.partDesignators[p];
					else if (SERIES_DESIGNATOR_TYPE.equals(partDesignatorType))
						bibRef.seriesDesignator = bibRef.partDesignators[p];
					else System.out.println("Unclassified part designator: " + bibRef.partDesignators[p].toXML());
				}
			}
			d = (e-1); // proceed at e, mind countering loop increment, though
		}
		
		if (DEBUG) {
			System.out.println("authorList: " + ((bibRef.authorList == null) ? "" : bibRef.authorList.getValue()));
			System.out.println("year: " + ((bibRef.year == null) ? "" : bibRef.year.getValue()));
			System.out.println("volume: " + ((bibRef.volumeDesignator == null) ? "" : bibRef.volumeDesignator.getValue()));
			System.out.println("issue: " + ((bibRef.issueDesignator == null) ? "" : bibRef.issueDesignator.getValue()));
			System.out.println("number: " + ((bibRef.numberDesignator == null) ? "" : bibRef.numberDesignator.getValue()));
			System.out.println("series: " + ((bibRef.seriesDesignator == null) ? "" : bibRef.seriesDesignator.getValue()));
			System.out.println("fascicle: " + ((bibRef.fascicleDesignator == null) ? "" : bibRef.fascicleDesignator.getValue()));
			System.out.println("page(s): " + ((bibRef.pagination == null) ? "" : bibRef.pagination.getValue()));
			System.out.println();
		}
	}
	
	//	TODOne adjust exponents values SEEMS TO WORK LIKE THIS
	private static final int matchExp = 3;
	private static final int subsumeExp = 2;
	private static final int getFuzzyScore(int sSize, String sString, LinkedHashSet sElements, CountingSet structureCounts, HashMap structureElementSets) {
		int fuzzyScore = 0;
		for (Iterator csit = structureElementSets.keySet().iterator(); csit.hasNext();) {
			String cString = ((String) csit.next());
			int fScore;
			
			//	structures equal, score like above
			if (cString.equals(sString))
//				fScore = (((int) Math.pow(sPunctSummaryElements.size(), 2)) * structureCounts.getCount(structure.typeString));
				fScore = (((int) Math.pow(sSize, matchExp)) * structureCounts.getCount(cString));
			
			//	try subsumption match
			else {
				LinkedHashSet cElements = ((LinkedHashSet) structureElementSets.get(cString));
				if (subsumes(cElements, sElements))
//					fScore = (((int) Math.pow(sSummaryElements.size(), 2)) * structureCounts.getCount(typeString));
//					fScore = (((int) Math.pow(structure.detailTypes.size(), 2)) * structureCounts.getCount(typeString));
					fScore = (((((int) Math.pow(sSize, subsumeExp)) * structureCounts.getCount(cString)) * sElements.size()) / cElements.size());
				else fScore = 0;
			}
			
			//	add score
//			fuzzyScore += fScore;
			fuzzyScore = Math.max(fuzzyScore, fScore);
		}
		
		//	finally ...
		return fuzzyScore;
	}
	
	private static boolean subsumes(LinkedHashSet higherStructure, LinkedHashSet lowerStructure) {
		
		//	lower structure larger than higher structure
		//	==> subsumption match impossible
		if (higherStructure.size() <= lowerStructure.size())
			return false;
		
		//	lower structure has elements not contained in higher structure
		//	==> subsumption match impossible
		if (!higherStructure.containsAll(lowerStructure))
			return false;
		
		//	check element order
		for (Iterator hsit = higherStructure.iterator(), lsit = lowerStructure.iterator(); hsit.hasNext();) {
			
			//	get next element of higher structure
			String hsElement = ((String) hsit.next());
			
			//	element not contained in lower structure
			//	==> ignore it
			if (!lowerStructure.contains(hsElement))
				continue;
			
			//	element contained in lower structure, has to be next in latter to not violate ordering condition
			//	==> if not, higher structure does not subsume lower structure
			if (!lsit.hasNext() || !hsElement.equals(lsit.next()))
				return false;
		}
		
		//	due to containsAll() pre-condition, there cannot be left anything in lower structure
		//	==> we have a subsumption match
		return true;
	}
	
	private String selectPrimarySeparator(BibRef[] bibRefs) {
		CountingSet separators = new CountingSet(new LinkedHashMap());
		
		//	count frequencies of separator chars
		for (int r = 0; r < bibRefs.length; r++)
			for (int s = 1; s < (bibRefs[r].structure.punctSummary.length - 1); s++) {
				if (Gamta.isPunctuation(bibRefs[r].structure.punctSummary[s])
					&&
					!"_".equals(bibRefs[r].structure.punctSummary[s])
					&&
					(
						Gamta.isWord(bibRefs[r].structure.punctSummary[s-1])
						||
						Gamta.isWord(bibRefs[r].structure.punctSummary[s+1])
					))
					separators.add(bibRefs[r].structure.punctSummary[s]);
			}
		if (DEBUG) System.out.println("Got " + separators.size() + " separators from " + bibRefs.length + " bibliographic references:");
		
		//	select most frequent separator
		String primarySeparator = "";
		int primarySeparatorFrequency = 0;
		for (Iterator sit = separators.iterator(); sit.hasNext();) {
			String separator = ((String) sit.next());
			int separatorFrequency = separators.getCount(separator);
			if (!Gamta.isBracket(separator) && (primarySeparatorFrequency < separatorFrequency)) {
				primarySeparator = separator;
				primarySeparatorFrequency = separatorFrequency;
			}
			if (DEBUG) System.out.println("  - " + separator + " (" + separatorFrequency + ")");
		}
		if (DEBUG) {
			System.out.println("  ==> primary separator: " + primarySeparator);
			System.out.println();
		}
		
		//	finally ...
		return primarySeparator;
	}
	
	private String selectTitleJournalPublisherSeparator(BibRef[] bibRefs) {
		
		//	count intermediate punctuation blocks in references with exactly two unassigned word blocks
		CountingSet tJopSeparators = new CountingSet(new LinkedHashMap());
		for (int r = 0; r < bibRefs.length; r++) {
			if (bibRefs[r].wordBlocks.length != 2)
				continue;
			boolean elementsBetween = false;
			for (int t = bibRefs[r].wordBlocks[0].getEndIndex(); t < bibRefs[r].wordBlocks[1].getStartIndex(); t++)
				if (bibRefs[r].wordBlockExcluded[t] || Gamta.isWord(bibRefs[r].annotation.valueAt(t)) || Gamta.isNumber(bibRefs[r].annotation.valueAt(t))) {
					elementsBetween = true;
					break;
				}
			if (elementsBetween)
				continue;
			String tJopSeparator = TokenSequenceUtils.concatTokens(bibRefs[r].annotation, bibRefs[r].wordBlocks[0].getEndIndex(), (bibRefs[r].wordBlocks[1].getStartIndex() - bibRefs[r].wordBlocks[0].getEndIndex()));
			tJopSeparators.add(tJopSeparator);
		}
		if (DEBUG) System.out.println("Got " + tJopSeparators.size() + " after-title separators from " + bibRefs.length + " bibliographic references:");
		
		//	find most frequent after-title separator
		String tJopSeparator = "";
		int tJopSeparatorFrequency = 0;
		for (Iterator sit = tJopSeparators.iterator(); sit.hasNext();) {
			String tJopSep = ((String) sit.next());
			int tJopSepFrequency = tJopSeparators.getCount(tJopSep);
			if (tJopSeparatorFrequency < tJopSepFrequency) {
				tJopSeparator = tJopSep;
				tJopSeparatorFrequency = tJopSepFrequency;
			}
			if (DEBUG) System.out.println("  - " + tJopSep + " (" + tJopSepFrequency + ")");
		}
		if ((tJopSeparatorFrequency * 5) < bibRefs.length) {
			tJopSeparator = "";
			if (DEBUG) {
				System.out.println("  ==> primary after-title separator not found, support too low");
				System.out.println();
			}
		}
		else if (DEBUG) {
			System.out.println("  ==> primary after-title separator: " + tJopSeparator);
			System.out.println();
		}
		
		//	finally ...
		return tJopSeparator;
	}
	
	private void extractVolumeReference(BibRef bibRef, String primarySeparator, AuthorListStyle authorListStyle, NameStyle nameStyle, DocumentStyle authorNameStyle) {
		
		//	get volume reference prefixes
		Annotation[] volumeReferencePrefixes = Gamta.extractAllMatches(bibRef.annotation, "[IiEe][Nn]\\:?", 2);
		if (volumeReferencePrefixes.length == 0)
			return;
		if (DEBUG) System.out.println("Seeking volume reference in " + bibRef.annotation.getValue());
		
		//	annotate volume reference
		Annotation volumeReferencePrefix = null;
		boolean gotEditorStart = false;
		for (int v = 0; v < volumeReferencePrefixes.length; v++) {
			if (DEBUG) System.out.println(" - investigating volume reference prefix " + volumeReferencePrefixes[v]);
			if (volumeReferencePrefixes[v].size() == 2) {
				if (DEBUG) System.out.println("   ==> safe with colon");
				volumeReferencePrefix = volumeReferencePrefixes[v];
				break;
			}
			
			if (volumeReferencePrefixes[v].getStartIndex() < 2)
				continue;
//			if (!primarySeparator.equals(bibRef.annotation.valueAt(volumeReferencePrefixes[v].getStartIndex() - 1))) {
//				if (DEBUG) System.out.println("==> no preceding separator");
//				continue;
//			}
			if ("\"".equals(bibRef.annotation.valueAt(volumeReferencePrefixes[v].getStartIndex() - 1))) {
				if (!primarySeparator.equals(bibRef.annotation.valueAt(volumeReferencePrefixes[v].getStartIndex() - 2)) && (".,?!".indexOf(bibRef.annotation.valueAt(volumeReferencePrefixes[v].getStartIndex() - 2)) == -1)) {
					if (DEBUG) System.out.println("   ==> no preceding separator");
					continue;
				}
			}
			else if (!primarySeparator.equals(bibRef.annotation.valueAt(volumeReferencePrefixes[v].getStartIndex() - 1)) && (".,?!".indexOf(bibRef.annotation.valueAt(volumeReferencePrefixes[v].getStartIndex() - 1)) == -1)) {
				if (DEBUG) System.out.println("   ==> no preceding separator");
				continue;
			}
			if (bibRef.annotation.size() <= volumeReferencePrefixes[v].getEndIndex())
				continue;
			
			//	try and find labeled editor list for confirmation
			Annotation volumeReferenceCandidate = Gamta.newAnnotation(bibRef.annotation, null, volumeReferencePrefixes[v].getEndIndex(), (bibRef.annotation.size() - volumeReferencePrefixes[v].getEndIndex()));
			Annotation[] editorNames = this.getAuthorNames(volumeReferenceCandidate, null, nameStyle);
			AuthorList[] editorLists = this.getAuthorLists(null, volumeReferenceCandidate, editorNames, authorNameStyle);
			AuthorList labeledEditorList = null;
			AuthorList styleCompatibleEditorList = null;
			if (DEBUG) System.out.println("   - checking editor lists:");
			for (int e = 0; e < editorLists.length; e++) {
				if (DEBUG) System.out.println("     - " + editorLists[e].annotation.toXML());
				if ((editorLists[e].editorListLabelPos == 'T') && (editorLists[e].annotation.getStartIndex() > 1)) {
					if (DEBUG) System.out.println("       ==> too late after prefix for tail-labeled editor list");
					continue;
				}
				
				//	check style for unlabeled editor lists
				if (editorLists[e].editorListLabel == null) {
					if ((authorListStyle == null) || authorListStyle.isCompatible(editorLists[e])) {
						if ((styleCompatibleEditorList == null) || AnnotationUtils.liesIn(styleCompatibleEditorList.annotation, editorLists[e].annotation))
							styleCompatibleEditorList = editorLists[e];
					}
					else {
						if (DEBUG) System.out.println("       ==> incompatible style");
						continue;
					}
				}
				
				//	let's assume we're safe with a label
				else if ((labeledEditorList == null) || AnnotationUtils.liesIn(labeledEditorList.annotation, editorLists[e].annotation))
					labeledEditorList = editorLists[e];
			}
			if (labeledEditorList != null) {
				if (DEBUG) System.out.println("   ==> found labeled editor list: " + labeledEditorList.annotation);
				volumeReferencePrefix = volumeReferencePrefixes[v];
				gotEditorStart = ((volumeReferencePrefix.getEndIndex() - labeledEditorList.annotation.getStartIndex()) < 2);
				break;
			}
			if (styleCompatibleEditorList != null) {
				if (DEBUG) System.out.println("   ==> found style compatible editor list: " + styleCompatibleEditorList.annotation);
				volumeReferencePrefix = volumeReferencePrefixes[v];
				gotEditorStart = ((volumeReferencePrefix.getEndIndex() - styleCompatibleEditorList.annotation.getStartIndex()) < 2);
				break;
			}
			
			//	try plain editor names as well
			Annotation[] editorListLabels = Gamta.extractAllMatches(volumeReferenceCandidate, this.editorListLabelRegEx);
			Annotation editor = null;
			if (DEBUG) System.out.println("   - checking editors:");
			for (int e = 0; e < editorNames.length; e++) {
				if (DEBUG) System.out.println("     - " + editorNames[e].toXML());
				if (editorNames[e].getStartIndex() > 1) {
					if (DEBUG) System.out.println("       ==> too late after prefix");
					continue;
				}
				if ((authorListStyle != null) && ((editorListLabels.length == 0) || ((editorListLabels[0].getStartIndex() - editorNames[e].getEndIndex()) > 4))) {
					String fns = ((String) editorNames[e].getAttribute(firstNameStyleAttribute));
					if ("N".equals(fns) && !authorListStyle.firstNameStyles.contains(fns)) {
						if (DEBUG) System.out.println("       ==> no initials");
						continue;
					}
				}
				if (editorNames[e].size() > (".".equals(editorNames[e].lastValue()) ? 2 : 1)) {
					editor = editorNames[e];
					break;
				}
				else if (DEBUG) System.out.println("       ==> too short");
			}
			if (editor == null) {
				if (DEBUG) System.out.println("   ==> no editors");
				continue;
			}
			else {
				if (DEBUG) System.out.println("   ==> found editor name: " + editor);
				volumeReferencePrefix = volumeReferencePrefixes[v];
				gotEditorStart = true;
				break;
			}
		}
		if (volumeReferencePrefix == null)
			return;
		
		//	find end of volume reference
		int volumeReferenceEnd = bibRef.annotation.size();
		
		//	exclude pagination
		if ((bibRef.pagination != null) && (volumeReferencePrefix.getEndIndex() < bibRef.pagination.getStartIndex())) {
			volumeReferenceEnd = Math.min(volumeReferenceEnd, bibRef.pagination.getStartIndex());
			volumeReferenceEnd = this.truncateVolumeReferencePunctuation(bibRef, volumeReferencePrefix.getEndIndex(), volumeReferenceEnd);
		}
		
		//	exclude year if late in reference
		if ((bibRef.year != null) && (volumeReferencePrefix.getEndIndex() < bibRef.year.getStartIndex())) {
			volumeReferenceEnd = Math.min(volumeReferenceEnd, bibRef.year.getStartIndex());
			volumeReferenceEnd = this.truncateVolumeReferencePunctuation(bibRef, volumeReferencePrefix.getEndIndex(), volumeReferenceEnd);
		}
		
		//	exclude part designator blocks (also prevents voting them out on structure, as most volume references are to books)
		if ((bibRef.numberDetailBlock != null) && (volumeReferencePrefix.getEndIndex() < bibRef.numberDetailBlock.getStartIndex())) {
			volumeReferenceEnd = Math.min(volumeReferenceEnd, bibRef.numberDetailBlock.getStartIndex());
			volumeReferenceEnd = this.truncateVolumeReferencePunctuation(bibRef, volumeReferencePrefix.getEndIndex(), volumeReferenceEnd);
		}
		
		//	annotate volume reference
		if (volumeReferencePrefix.getEndIndex() < volumeReferenceEnd) {
			bibRef.volumeReferencePrefix = volumeReferencePrefix;
			bibRef.volumeReference = Gamta.newAnnotation(bibRef.annotation, VOLUME_REFERENCE_ANNOTATION_TYPE, volumeReferencePrefix.getEndIndex(), (volumeReferenceEnd - volumeReferencePrefix.getEndIndex()));
			if (gotEditorStart)
				bibRef.volumeReference.setAttribute("editorStart", "true");
			for (int t = -volumeReferencePrefix.size(); t < bibRef.volumeReference.size(); t++)// include 'In'
				bibRef.structure.details[bibRef.volumeReference.getStartIndex() + t] = VOLUME_REFERENCE_ANNOTATION_TYPE;
			if (DEBUG) {
				System.out.println("Got volume reference in " + bibRef.annotation.getValue() + ":");
				System.out.println("  " + bibRef.volumeReference.getValue());
			}
			
			//	clean up part designators located before volume reference
			bibRef.volumeDesignator = this.reSelectPartDesignator(bibRef.annotation, bibRef.volumeDesignators, bibRef.partDesignators, VOLUME_DESIGNATOR_TYPE, bibRef.volumeReference, bibRef.structure.details);
			if (DEBUG) System.out.println("   ==> volume designator set to " + bibRef.volumeDesignator);
			bibRef.issueDesignator = this.reSelectPartDesignator(bibRef.annotation, bibRef.issueDesignators, bibRef.partDesignators, ISSUE_DESIGNATOR_TYPE, bibRef.volumeReference, bibRef.structure.details);
			if (DEBUG) System.out.println("   ==> issue designator set to " + bibRef.issueDesignator);
			bibRef.numberDesignator = this.reSelectPartDesignator(bibRef.annotation, bibRef.numberDesignators, bibRef.partDesignators, NUMBER_DESIGNATOR_TYPE, bibRef.volumeReference, bibRef.structure.details);
			if (DEBUG) System.out.println("   ==> number designator set to " + bibRef.numberDesignator);
		}
	}
	
	private int truncateVolumeReferencePunctuation(BibRef bibRef, int volumeReferencePrefixEnd, int volumeReferenceEnd) {
		while (volumeReferenceEnd > 0) {
			String vrEndToken = bibRef.annotation.valueAt(volumeReferenceEnd-1);
			
			//	retain closing bracket if opening counterpart just ahead
			if (Gamta.isClosingBracket(vrEndToken)) {
				boolean gotOpeningBracket = false;
				for (int t = (volumeReferenceEnd-2); t >= volumeReferencePrefixEnd; t--) {
					if (Gamta.opens(bibRef.annotation.valueAt(t), vrEndToken)) {
						gotOpeningBracket = true;
						break;
					}
					else if (Gamta.isClosingBracket(bibRef.annotation.valueAt(t)))
						break;
				}
				if (gotOpeningBracket)
					break;
				else volumeReferenceEnd--;
			}
			
			//	truncate other punctuation marks
			else if (Gamta.isPunctuation(vrEndToken))
				volumeReferenceEnd--;
			
			//	retain any non-punctuation tokens
			else break;
		}
		return volumeReferenceEnd;
	}
	
	private Annotation reSelectPartDesignator(Annotation bibRef, Annotation[] partDesignators, Annotation[] allPartDesignators, String partDesignatorType, Annotation journalOrPublisher, String[] structureDetails) {
		if ((partDesignators == null) || (partDesignators.length == 0))
			return null;
		
		//	mark part designator tokens
		boolean[] isPartDesignator = new boolean[bibRef.size()];
		Arrays.fill(isPartDesignator, false);
		for (int d = 0; d < allPartDesignators.length; d++) {
			for (int t = allPartDesignators[d].getStartIndex(); t < allPartDesignators[d].getEndIndex(); t++)
				isPartDesignator[t] = true;
		}
		
		//	select first part designator of given type after end of journal / publisher
		Annotation partDesignator = null;
		for (int p = 0; p < partDesignators.length; p++) {
			System.out.println("Assessing " + partDesignators[p].getValue());
			if ((partDesignators[p].getStartIndex() < journalOrPublisher.getEndIndex()) || (partDesignator != null)) {
				System.out.println("  ==> too early, cleaning up");
				for (int d = partDesignators[p].getStartIndex(); d < partDesignators[p].getEndIndex(); d++) {
					if (PART_DESIGNATOR_ANNOTATION_TYPE.equals(structureDetails[d]))
						structureDetails[d] = "_";
				}
				for (int d = (partDesignators[p].getStartIndex() - 1); d > -1; d--) {
					if (!PART_DESIGNATOR_ANNOTATION_TYPE.equals(structureDetails[d]))
						break;
					if (isPartDesignator[d])
						break;
					structureDetails[d] = "_";
				}
			}
			else if (partDesignator == null) {
				System.out.println("  ==> might fit");
				boolean partDesignatorFits = true;
				for (int d = partDesignators[p].getStartIndex(); d < partDesignators[p].getEndIndex(); d++)
					if (!"_".equals(structureDetails[d]) && !PART_DESIGNATOR_ANNOTATION_TYPE.equals(structureDetails[d])) {
						partDesignatorFits = false;
						break;
					}
				if (partDesignatorFits) {
					System.out.println("  ==> does fit");
					partDesignator = partDesignators[p];
					for (int d = partDesignator.getStartIndex(); d < partDesignator.getEndIndex(); d++)
						structureDetails[d] = PART_DESIGNATOR_ANNOTATION_TYPE;
				}
				else System.out.println("  ==> interfers with some other number");
			}
		}
		if (partDesignator != null)
			return partDesignator;
		
		//	select first generic part designator after end of journal / publisher
		for (int p = 0; p < allPartDesignators.length; p++) {
			if (!partDesignatorType.equals(allPartDesignators[p].getAttribute(TYPE_ATTRIBUTE, partDesignatorType)))
				continue;
			System.out.println("Assessing " + allPartDesignators[p].getValue());
			if ((allPartDesignators[p].getStartIndex() < journalOrPublisher.getEndIndex()) || (partDesignator != null)) {
				System.out.println("  ==> too early, cleaning up");
				for (int d = allPartDesignators[p].getStartIndex(); d < allPartDesignators[p].getEndIndex(); d++) {
					if (PART_DESIGNATOR_ANNOTATION_TYPE.equals(structureDetails[d]))
						structureDetails[d] = "_";
				}
				for (int d = (allPartDesignators[p].getStartIndex() - 1); d > -1; d--) {
					if (!PART_DESIGNATOR_ANNOTATION_TYPE.equals(structureDetails[d]))
						break;
					if (isPartDesignator[d])
						break;
					structureDetails[d] = "_";
				}
			}
			else if (partDesignator == null) {
				System.out.println("  ==> might fit");
				boolean partDesignatorFits = true;
				for (int d = allPartDesignators[p].getStartIndex(); d < allPartDesignators[p].getEndIndex(); d++)
					if (!"_".equals(structureDetails[d]) && !PART_DESIGNATOR_ANNOTATION_TYPE.equals(structureDetails[d])) {
						partDesignatorFits = false;
						break;
					}
				if (partDesignatorFits) {
					System.out.println("  ==> does fit");
					partDesignator = allPartDesignators[p];
					partDesignator.setAttribute(TYPE_ATTRIBUTE, partDesignatorType);
					for (int d = partDesignator.getStartIndex(); d < partDesignator.getEndIndex(); d++)
						structureDetails[d] = PART_DESIGNATOR_ANNOTATION_TYPE;
				}
				else System.out.println("  ==> interfers with some other number");
			}
		}
		return partDesignator;
	}
	
	private void selectTitleJournalPublisher(BibRef bibRef, String tJopSeparator, TokenSequence tJopSeparatorTokens, BibRef[] bibRefs, boolean isRecursiveCall) {
		if (!isRecursiveCall && DEBUG) System.out.println("Getting title and JoP from " + bibRef.annotation.toXML());
		
		//	select title, journal/publisher, and volume title
		this.selectTitleJournalPublisher(bibRef, tJopSeparator, tJopSeparatorTokens, bibRefs);
		
		//	trim punctuation
		bibRef.title = this.truncatePunctuation(bibRef.annotation, bibRef.title, "", "?!");
		bibRef.volumeTitle = this.truncatePunctuation(bibRef.annotation, bibRef.volumeTitle, "", "?!");
		bibRef.journalOrPublisher = this.truncatePunctuation(bibRef.annotation, bibRef.journalOrPublisher, "", "");
		
		//	include tailing question and exclamation marks in title (they do have some semantics)
		bibRef.title = this.includeTailingPunctuation(bibRef, bibRef.title, "?!");
		
		//	include tailing dots in journal names (they do belong to the abbreviations)
		if ((bibRef.journalOrPublisher != null) && (bibRef.volumeDesignator != null) || (bibRef.issueDesignator != null) || (bibRef.numberDesignator != null))
			bibRef.journalOrPublisher = this.includeTailingPunctuation(bibRef, bibRef.journalOrPublisher, ".");
		
		//	no need to go through all the hassle if we have a number detail block
		if (bibRef.numberDetailBlock != null)
			return;
		
		//	no need to circle back twice
		if (isRecursiveCall)
			return;
		
		//	copy (current) structure details and add title, journal or publisher, volume title, and editors
		String[] detailTypes = new String[bibRef.structure.details.length];
		System.arraycopy(bibRef.structure.details, 0, detailTypes, 0, bibRef.structure.details.length);
		if (bibRef.title != null)
			Arrays.fill(detailTypes, bibRef.title.getStartIndex(), bibRef.title.getEndIndex(), TITLE_ANNOTATION_TYPE);
		if (bibRef.journalOrPublisher != null)
			Arrays.fill(detailTypes, bibRef.journalOrPublisher.getStartIndex(), bibRef.journalOrPublisher.getEndIndex(), JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE);
		if (bibRef.volumeTitle != null)
			Arrays.fill(detailTypes, bibRef.volumeTitle.getStartIndex(), bibRef.volumeTitle.getEndIndex(), VOLUME_TITLE_ANNOTATION_TYPE);
		if (bibRef.editors != null) {
			for (int e = 0; e < bibRef.editors.length; e++)
				Arrays.fill(detailTypes, bibRef.editors[e].getStartIndex(), bibRef.editors[e].getEndIndex(), EDITOR_LIST_ANNOTATION_TYPE);
		}
		
		//	add DOIs and URLs
		if (bibRef.dois != null) {
			for (int d = 0; d < bibRef.dois.length; d++)
				Arrays.fill(detailTypes, bibRef.dois[d].getStartIndex(), bibRef.dois[d].getEndIndex(), PUBLICATION_DOI_ANNOTATION_TYPE);
		}
		if (bibRef.urls != null) {
			for (int u = 0; u < bibRef.urls.length; u++)
				Arrays.fill(detailTypes, bibRef.urls[u].getStartIndex(), bibRef.urls[u].getEndIndex(), PUBLICATION_URL_ANNOTATION_TYPE);
		}
		
		//	get rid of volume reference (or whatever is left of it)
		AnnotationFilter.removeAnnotations(bibRef.annotation, VOLUME_REFERENCE_ANNOTATION_TYPE);
		for (int t = 0; t < bibRef.annotation.size(); t++) {
			if (VOLUME_REFERENCE_ANNOTATION_TYPE.equals(detailTypes[t]))
				detailTypes[t] = "_";
		}
		
		//	make damn sure to not add volume reference label to title, though ...
		if (bibRef.volumeReferencePrefix != null)
			Arrays.fill(detailTypes, bibRef.volumeReferencePrefix.getStartIndex(), bibRef.volumeReferencePrefix.getEndIndex(), VOLUME_REFERENCE_ANNOTATION_TYPE);
		
		//	track detail removal (not re-designation)
		int blankTokenCountBefore = 0;
		for (int t = 0; t < bibRef.annotation.size(); t++) {
			if ("_".equals(detailTypes[t]))
				blankTokenCountBefore++;
		}
		
		//	run detail type order filter on number details
		if (DEBUG) System.out.println("Order-filtering number details in " + bibRef.annotation.toXML());
		this.filterNumberDetailsByDetailOrder(bibRef, detailTypes);
		
		//	check for detail removal (not re-designation)
		int blankTokenCountAfter = 0;
		for (int t = 0; t < bibRef.annotation.size(); t++) {
			if ("_".equals(detailTypes[t]))
				blankTokenCountAfter++;
		}
		
		//	anything removed?
		if (blankTokenCountAfter == blankTokenCountBefore) {
			if (DEBUG) System.out.println(" ==> word blocks unchanged");
			return;
		}
		if (DEBUG) System.out.println(" ==> cleared " + (blankTokenCountAfter - blankTokenCountBefore) + " tokens");
		
		//	adjust main structure
		for (int t = 0; t < bibRef.annotation.size(); t++) {
			if (detailTypes[t].equals(bibRef.structure.details[t]))
				continue;
			if ("_".equals(detailTypes[t]))
				bibRef.structure.details[t] = "_";
			else if (PART_DESIGNATOR_ANNOTATION_TYPE.equals(detailTypes[t]))
				bibRef.structure.details[t] = detailTypes[t];
		}
		
		//	reset reference
		bibRef.wordBlockExcluded = null;
		bibRef.wordBlocks = null;
		bibRef.title = null;
		bibRef.journalOrPublisher = null;
		bibRef.volumeTitle = null;
		
		//	re-get word blocks
		this.getWordBlocks(bibRef, bibRef.structure.details);
		if (DEBUG) {
			System.out.println("Re-fetched word blocks:");
			for (int b = 0; b < bibRef.wordBlocks.length; b++)
				System.out.println(" - " + bibRef.wordBlocks[b].getValue());
		}
		
		//	start over
		this.selectTitleJournalPublisher(bibRef, tJopSeparator, tJopSeparatorTokens, bibRefs, true);
	}
	
	private void selectTitleJournalPublisher(BibRef bibRef, String tJopSeparator, TokenSequence tJopSeparatorTokens, BibRef[] bibRefs) {
		if (bibRef.wordBlocks.length == 0)
			return;
		
		//	rule: one block ==> title TODO for references without punctuation, try and find tailing title case block in title if no URL given (better than no journal/publisher at all)
		if (bibRef.wordBlocks.length == 1) {
			bibRef.title = bibRef.wordBlocks[0];
			bibRef.title.changeTypeTo(TITLE_ANNOTATION_TYPE);
			if (DEBUG) System.out.println("Got single-block title: '" + bibRef.title + "'");
			return;
		}
		
		//	mark which word blocks can be merged and which cannot
		boolean[] canMergeWithSuccessor = new boolean[bibRef.wordBlocks.length];
		boolean canMergeAll = true;
		Arrays.fill(canMergeWithSuccessor, true);
		if (DEBUG) System.out.println("Assessing word block mergeability:");
		for (int b = 0; b < (bibRef.wordBlocks.length-1); b++) {
			if (DEBUG) System.out.println(" - checking '" + bibRef.wordBlocks[b].getValue() + "' and '" + bibRef.wordBlocks[b+1].getValue() + "'");
			for (int t = bibRef.wordBlocks[b].getEndIndex(); t < bibRef.wordBlocks[b+1].getStartIndex(); t++)
				if (bibRef.wordBlockExcluded[t]) {
					canMergeWithSuccessor[b] = false;
					canMergeAll = false;
					if (DEBUG) System.out.println("   ==> not mergeable due to " + bibRef.structure.details[t] + " '" + bibRef.annotation.valueAt(t) + "'");
					break;
				}
			if (DEBUG && canMergeWithSuccessor[b])
				System.out.println("   ==> mergeable");
		}
		
		//	with a URL present, mark which word blocks must be in (web site) title by all means
		boolean[] isWebSiteTitle = new boolean[bibRef.wordBlocks.length];
		Arrays.fill(isWebSiteTitle, false);
		if (bibRef.urls.length > bibRef.dois.length) {
			if (DEBUG) System.out.println("Assessing word block to title predetermination:");
			for (int b = 0; b < bibRef.wordBlocks.length; b++) {
				if (DEBUG) System.out.println(" - checking '" + bibRef.wordBlocks[b].getValue() + "'");
				for (int t = bibRef.wordBlocks[b].getStartIndex(); t < bibRef.wordBlocks[b].getEndIndex(); t++)
					if (this.journalPublisherExcluded.containsIgnoreCase(bibRef.annotation.valueAt(t))) {
						isWebSiteTitle[b] = true;
						if (DEBUG) System.out.println("   ==> has to be in web site title due to '" + bibRef.annotation.valueAt(t) + "'");
						break;
					}
				if (isWebSiteTitle[b]) {
					for (int fb = (b-1); fb >= 0; fb--) {
						if (canMergeWithSuccessor[fb])
							isWebSiteTitle[fb] = true;
						else break;
					}
				}
				else if (DEBUG) System.out.println("   ==> OK for title and JoP");
			}
		}
		
		//	rule: if we have only a web site title, just use it as is
		if (canMergeAll && isWebSiteTitle[isWebSiteTitle.length - 1]) {
			bibRef.title = Gamta.newAnnotation(bibRef.annotation, TITLE_ANNOTATION_TYPE, bibRef.wordBlocks[0].getStartIndex(), (bibRef.wordBlocks[bibRef.wordBlocks.length-1].getEndIndex() - bibRef.wordBlocks[0].getStartIndex()));
			if (DEBUG) System.out.println("Got full span web site title: '" + bibRef.title + "'");
			return;
		}
		
		//	rule: two blocks ==> title, journal/publisher (or united in a website title)
		if (bibRef.wordBlocks.length == 2) {
			bibRef.title = bibRef.wordBlocks[0];
			bibRef.title.changeTypeTo(TITLE_ANNOTATION_TYPE);
			if (DEBUG) System.out.println("Got single-block title: '" + bibRef.title + "'");
			bibRef.journalOrPublisher = bibRef.wordBlocks[1];
			bibRef.journalOrPublisher.changeTypeTo(JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE);
			if (DEBUG) System.out.println("Got single-block JoP: '" + bibRef.journalOrPublisher + "'");
			return;
		}
		
		//	get known journal names and publishers 
		Annotation[] knownJops = this.getKnownJops(bibRef);
		
		//	get proceedings titles
		Annotation[] proceedingsTitles = this.getProceedingsTitles(bibRef);
		
		//	assess where journal/publisher might be
		int minJournalStart = 0;
		int maxJournalEnd = bibRef.annotation.size();
		int partDesCount = 0;
		int minPublisherStart = 0;
		int maxPublisherEnd = bibRef.annotation.size();
		
		//	check book content hints
		if (bibRef.bookContentInfos.size() != 0) {
			for (int h = 0; h < bibRef.bookContentInfos.size(); h++)
				maxPublisherEnd = Math.min(maxPublisherEnd, ((Annotation) bibRef.bookContentInfos.get(h)).getStartIndex());
		}
		
		//	check journal part designators
		else {
			if (bibRef.volumeDesignator != null) {
				maxJournalEnd = Math.min(maxJournalEnd, bibRef.volumeDesignator.getStartIndex());
				partDesCount++;
			}
			if (bibRef.issueDesignator != null) {
				maxJournalEnd = Math.min(maxJournalEnd, bibRef.issueDesignator.getStartIndex());
				partDesCount++;
			}
			if (bibRef.numberDesignator != null) {
				maxJournalEnd = Math.min(maxJournalEnd, bibRef.numberDesignator.getStartIndex());
				partDesCount++;
			}
			
			//	if secure (range) pagination present and part designator far from pagination, use pagination as limit (catches un-recognized title numbers mistaken for part designators)
			if ((partDesCount != 0) && (bibRef.pagination != null) && (bibRef.pagination.size() > 1) && (maxJournalEnd < (bibRef.pagination.getStartIndex() - (4 * partDesCount)))) {
				maxJournalEnd = bibRef.pagination.getStartIndex();
				partDesCount = 0;
			}
		}
		
		//	score word blocks
		float[] wordBlockScores = new float[bibRef.wordBlocks.length];
		float wordBlockScoreSum = 0;
		int wordBlockWordCount = 0;
		if (DEBUG) System.out.println("Scoring word blocks:");
		for (int b = 0; b < bibRef.wordBlocks.length; b++) {
			wordBlockScores[b] = this.getJopScore(bibRef.wordBlocks[b]);
			if (DEBUG) System.out.println(" - " + bibRef.wordBlocks[b].getValue() + " ==> " + wordBlockScores[b]);
			wordBlockScoreSum += wordBlockScores[b];
			wordBlockWordCount += bibRef.wordBlocks[b].size();
		}
		
		//	smooth scores
		if (DEBUG) System.out.println("Smoothing word block scores:");
		for (int b = 0; b < bibRef.wordBlocks.length; b++) {
			if (wordBlockScores[b] == 0)
//				wordBlockScores[b] = (wordBlockScoreSum / (2 * bibRef.wordBlocks.length)); // TODOne use number of tokens in word blocks instead
				wordBlockScores[b] = (wordBlockScoreSum / wordBlockWordCount);
			if (DEBUG) System.out.println(" - " + bibRef.wordBlocks[b].getValue() + " ==> " + wordBlockScores[b]);
		}
		
		//	collect mergeable sequences of word blocks, and score possible splits
		float[] splitAfterWordBlockScores = new float[bibRef.wordBlocks.length];
		Arrays.fill(splitAfterWordBlockScores, 0);
		int wbi = 0;
		if (DEBUG) System.out.println("Assessing word block groupings and splits:");
		while (wbi < bibRef.wordBlocks.length) {
			if (!canMergeWithSuccessor[wbi]) {
				wbi++;
				continue;
			}
			int swbi = wbi;
			while ((wbi < bibRef.wordBlocks.length) && ((wbi == swbi) || canMergeWithSuccessor[wbi-1]))
				wbi++;
			if ((wbi - swbi) >= 3) {
				if (DEBUG) {
					System.out.println(" - investigating group of " + (wbi - swbi) + " word blocks:");
					for (int b = swbi; b < wbi; b++)
						System.out.println("   - " + bibRef.wordBlocks[b].getValue() + " (" + wordBlockScores[b] + ")");
				}
				float zeroDenominatorFallback = (1.0f / (bibRef.wordBlocks[wbi-1].getEndIndex() - bibRef.wordBlocks[swbi].getStartIndex()));
				for (int s = swbi; s < (wbi-1); s++) {
					
					//	score left side of split
					float scoreBeforeSplit = 0;
//					for (int b = swbi; b <= s; b++)
//						scoreBeforeSplit += wordBlockScores[b];
//					scoreBeforeSplit /= (s-swbi+1);
					for (int b = swbi; b <= s; b++)
						scoreBeforeSplit += (wordBlockScores[b] * bibRef.wordBlocks[b].size());
					scoreBeforeSplit /= (bibRef.wordBlocks[s].getEndIndex() - bibRef.wordBlocks[swbi].getStartIndex());
					float italicsBeforeSplit = 0;
					for (int t = bibRef.wordBlocks[swbi].getStartIndex(); t < bibRef.wordBlocks[s].getEndIndex(); t++) {
						if (bibRef.italicsToken[t])
							italicsBeforeSplit++;
					}
					italicsBeforeSplit /= (bibRef.wordBlocks[s].getEndIndex() - bibRef.wordBlocks[swbi].getStartIndex());
					
					//	score right side of split
					float scoreAfterSplit = 0;
//					for (int a = (s+1); a < wbi; a++)
//						scoreAfterSplit += wordBlockScores[a];
//					scoreAfterSplit /= (wbi-s-1);
					for (int a = (s+1); a < wbi; a++)
						scoreAfterSplit += (wordBlockScores[a] * bibRef.wordBlocks[a].size());
					scoreAfterSplit /= (bibRef.wordBlocks[wbi-1].getEndIndex() - bibRef.wordBlocks[s+1].getStartIndex());
					float italicsAfterSplit = 0;
					for (int t = bibRef.wordBlocks[s+1].getStartIndex(); t < bibRef.wordBlocks[wbi-1].getEndIndex(); t++) {
						if (bibRef.italicsToken[t])
							italicsAfterSplit++;
					}
					italicsAfterSplit /= (bibRef.wordBlocks[wbi-1].getEndIndex() - bibRef.wordBlocks[s+1].getStartIndex());
					
					//	penalize word repetitions on right side of split (words barely ever repeat in journal or publisher names)
					TreeSet afterSplitWords = new TreeSet(String.CASE_INSENSITIVE_ORDER);
					TreeSet afterSplitWordsDotted = new TreeSet(String.CASE_INSENSITIVE_ORDER);
					float afterSplitWordRepetitionPenalty = 1;
					for (int a = (s+1); a < wbi; a++)
						for (int t = bibRef.wordBlocks[a].getStartIndex(); t < bibRef.wordBlocks[a].getEndIndex(); t++) {
							String token = bibRef.annotation.valueAt(t);
							if (!Gamta.isWord(token))
								continue; // we're only after duplicate words
							if (token.length() < 3)
								continue; // we're not interested in all too short words
							boolean tokenDotted = (((t+1) < bibRef.annotation.size()) && ".".equals(bibRef.annotation.valueAt(t+1)));
							if (afterSplitWords.add(token)) {
								if (tokenDotted)
									afterSplitWordsDotted.add(token);
								continue; // we didn't see this one before
							}
							if (token.equals(token.toLowerCase()))
								continue; // we're not interested in lower case words (if in capitalized repetitions of theirs)
							afterSplitWordRepetitionPenalty /= token.length(); // penalize repetition by length of word
							if (tokenDotted != afterSplitWordsDotted.contains(token))
								afterSplitWordRepetitionPenalty /= 2; // double-penalize uneven abbreviation
						}
					
					//	==> product of average quotient and boundary quotient seems to be pretty good indicator
					//		- average quotient = discrimination between blocks of different type
					//		- boundary quotient = entropy of split at specific block boundary
//					splitAfterWordBlockScores[s] = (((scoreBeforeSplit == 0) ? 1 : (scoreAfterSplit/scoreBeforeSplit)) * ((wordBlockScores[s] == 0) ? 1 : (wordBlockScores[s+1]/wordBlockScores[s])));
//					splitAfterWordBlockScores[s] = ((scoreAfterSplit / ((scoreBeforeSplit == 0) ? zeroDenominatorFallback : scoreBeforeSplit)) * (wordBlockScores[s+1] / ((wordBlockScores[s] == 0) ? zeroDenominatorFallback : wordBlockScores[s])));
					float wordFrequencyScore = ((scoreAfterSplit / ((scoreBeforeSplit == 0) ? zeroDenominatorFallback : scoreBeforeSplit)) * (wordBlockScores[s+1] / ((wordBlockScores[s] == 0) ? zeroDenominatorFallback : wordBlockScores[s])));
					float wordLayoutScore = Math.max(italicsBeforeSplit, italicsAfterSplit) / Math.max(zeroDenominatorFallback, Math.min(italicsBeforeSplit, italicsAfterSplit));
					splitAfterWordBlockScores[s] = (wordFrequencyScore + wordLayoutScore) * afterSplitWordRepetitionPenalty;
					if (DEBUG) {
						System.out.print(" - split");
						System.out.print(" " + TokenSequenceUtils.concatTokens(bibRef.annotation, bibRef.wordBlocks[swbi].getStartIndex(), (bibRef.wordBlocks[s].getEndIndex() - bibRef.wordBlocks[swbi].getStartIndex())));
						System.out.print("     " + TokenSequenceUtils.concatTokens(bibRef.annotation, bibRef.wordBlocks[s+1].getStartIndex(), (bibRef.wordBlocks[wbi-1].getEndIndex() - bibRef.wordBlocks[s+1].getStartIndex())));
						System.out.println(":");
						System.out.println("   ==> average difference: " + (scoreAfterSplit-scoreBeforeSplit));
//						System.out.println("   ==> average quotient: " + ((scoreBeforeSplit == 0) ? 1 : (scoreAfterSplit/scoreBeforeSplit)));
						System.out.println("   ==> average quotient: " + (scoreAfterSplit / ((scoreBeforeSplit == 0) ? zeroDenominatorFallback : scoreBeforeSplit)));
						System.out.println("   ==> boundary difference: " + (wordBlockScores[s+1]-wordBlockScores[s]));
//						System.out.println("   ==> boundary quotient: " + ((wordBlockScores[s] == 0) ? 1 : (wordBlockScores[s+1]/wordBlockScores[s])));
						System.out.println("   ==> boundary quotient: " + (wordBlockScores[s+1] / ((wordBlockScores[s] == 0) ? zeroDenominatorFallback : wordBlockScores[s])));
						System.out.println("   ==> italics difference: " + Math.abs(italicsBeforeSplit - italicsAfterSplit));
						System.out.println("   ==> italics quotient: " + Math.max(italicsBeforeSplit, italicsAfterSplit) / Math.max(zeroDenominatorFallback, Math.min(italicsBeforeSplit, italicsAfterSplit)));
						System.out.println("   ==> after split word repetition penalty is: " + afterSplitWordRepetitionPenalty);
						System.out.println("   ==> score: " + splitAfterWordBlockScores[s] + " = (" + wordFrequencyScore + " + " + wordLayoutScore + ") * " + afterSplitWordRepetitionPenalty);
					}
				}
			}
			else if (DEBUG) System.out.println(" - skipping group of " + (wbi - swbi) + " word blocks");
		}
		
		//	exclude blocks with two or more digit numbers from journal names (i.e., only if volume designator given)
		if (partDesCount != 0)
			for (int b = 0; b < (bibRef.wordBlocks.length-1); b++) {
				if (bibRef.wordBlocks[b].getEndIndex() >= maxJournalEnd)
					break;
				boolean gotNumber = false;
				for (int t = 0; t < bibRef.wordBlocks[b].size(); t++)
					if ((bibRef.wordBlocks[b].valueAt(t).length() > 1) && Gamta.isNumber(bibRef.wordBlocks[b].valueAt(t))) {
						gotNumber = true;
						break;
					}
				if (gotNumber) {
					minJournalStart = bibRef.wordBlocks[b].getEndIndex();
					if (DEBUG) System.out.println("Word block excluded from journal name: " + bibRef.wordBlocks[b].getValue());
				}
			}
		
		//	exclude blocks that have to be in (web site) title from JoP
		for (int b = 0; b < bibRef.wordBlocks.length; b++) {
			if (bibRef.wordBlocks[b].getEndIndex() >= maxJournalEnd)
				break;
			if (isWebSiteTitle[b]) {
				minJournalStart = bibRef.wordBlocks[b].getEndIndex();
				minPublisherStart = bibRef.wordBlocks[b].getEndIndex();
				if (DEBUG) System.out.println("Word block excluded from JoP: " + bibRef.wordBlocks[b].getValue());
			}
		}
		
		//	prevent lone numbers (word blocks without actual words) from becoming titles by themselves ('1984' is rarely gonna be cited in science)
		for (int b = 0; b < bibRef.wordBlocks.length; b++) {
			if ((bibRef.bookContentInfos.size() != 0) && (bibRef.wordBlocks[b].getEndIndex() > maxPublisherEnd))
				break;
			if ((partDesCount != 0) && (bibRef.wordBlocks[b].getEndIndex() > maxJournalEnd))
				break;
			boolean gotWord = false;
			for (int t = 0; t < bibRef.wordBlocks[b].size(); t++)
				if ((bibRef.wordBlocks[b].valueAt(t).length() > 1) && Gamta.isWord(bibRef.wordBlocks[b].valueAt(t))) {
					gotWord = true;
					break;
				}
			if (gotWord) {
				minJournalStart = Math.max(minJournalStart, bibRef.wordBlocks[b].getEndIndex());
				minPublisherStart = Math.max(minPublisherStart, bibRef.wordBlocks[b].getEndIndex());
				if (DEBUG) System.out.println("First block containing word included in title: " + bibRef.wordBlocks[b].getValue());
				break;
			}
		}
		
		//	set up classification
		String[] wordBlockMeanings = new String[bibRef.wordBlocks.length];
		Arrays.fill(wordBlockMeanings, null);
		if (DEBUG) System.out.println("Classifying word blocks in " + bibRef.annotation);
		
		//	no volume reference
		if (bibRef.volumeRef == null) {
			if (DEBUG) System.out.println(" - no volume reference given");
			
			//	find last possible start of journal/publisher
			int lJopBlockIndex = 1;
			while ((lJopBlockIndex < isWebSiteTitle.length) && isWebSiteTitle[lJopBlockIndex])
				lJopBlockIndex++;
			if (DEBUG && (lJopBlockIndex < isWebSiteTitle.length)) System.out.println(" - got initial JoP start: '" + bibRef.wordBlocks[lJopBlockIndex].getValue() + "'");
			
			//	TODO set lJopBlockIndex to start of earliest known JoP
			if (knownJops.length != 0) {
				
				//	rule: no pagination, and known block after proceedings ==> proceedings become title, block afterward becomes publisher (likely reference to proceedings volume)
				
				//	rule: if pagination given, proceedings title and everything after becomes JoP
				
				//	rule: if separator punctutation given and present before proceedings, proceedings title becomes JoP
				
				//	rule: if separator punctutation given and present after proceedings, proceedings title becomes volume title, part afterward become publisher
				
			}
			
			//	TODO restrict to earliest known JoP with separator punctuation before it if latter given
			
			//	rule: if we have a proceedings title, use it and everything after as JoP, but don't expand rightward
			if (proceedingsTitles.length != 0) {
				if (DEBUG) System.out.println(" - got proceedings title: '" + proceedingsTitles[proceedingsTitles.length-1].getValue() + "'");
				for (int b = 0; b < bibRef.wordBlocks.length; b++) {
					if ((bibRef.bookContentInfos.size() != 0) && (bibRef.wordBlocks[b].getEndIndex() > maxPublisherEnd) && (bibRef.wordBlocks[lJopBlockIndex].getStartIndex() < maxPublisherEnd))
						continue;
					if ((partDesCount != 0) && (bibRef.wordBlocks[b].getEndIndex() > maxJournalEnd) && (bibRef.wordBlocks[lJopBlockIndex].getStartIndex() < maxJournalEnd))
						continue;
					if (bibRef.wordBlocks[b].getEndIndex() < proceedingsTitles[proceedingsTitles.length-1].getStartIndex())
						wordBlockMeanings[b] = TITLE_ANNOTATION_TYPE;
					else wordBlockMeanings[b] = JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE;
				}
			}
			
			//	rule: if we have only a web site title, just use it as is
			else if (isWebSiteTitle[isWebSiteTitle.length - 1]) {
				if (DEBUG) System.out.println(" - got web site title: '" + TokenSequenceUtils.concatTokens(bibRef.annotation, bibRef.wordBlocks[0].getStartIndex(), (bibRef.wordBlocks[bibRef.wordBlocks.length-1].getEndIndex() - bibRef.wordBlocks[0].getStartIndex())) + "'");
				Arrays.fill(wordBlockMeanings, TITLE_ANNOTATION_TYPE);
			}
			
			//	no proceedings title, spanning web site title, or known JoP given, use fuzzy rules
			else {
				
				//	rule: last capitalized block preceding part designator ==> latest possible start for journal/publisher
				if (DEBUG) System.out.println(" - seeking latest possible JoP start");
				for (int b = (bibRef.wordBlocks.length-1); b >= 1; b--) {
					if (bibRef.wordBlocks[b].getStartIndex() < Math.max(minJournalStart, minPublisherStart)) {
						if (DEBUG) System.out.println(" - giving up at block starting before " + Math.max(minJournalStart, minPublisherStart) + ": '" + bibRef.wordBlocks[b].getValue() + "'");
						break;
					}
					if ((bibRef.bookContentInfos.size() != 0) && (bibRef.wordBlocks[b].getEndIndex() > maxPublisherEnd) && (bibRef.wordBlocks[lJopBlockIndex].getStartIndex() < maxPublisherEnd))
						continue;
					if ((partDesCount != 0) && (bibRef.wordBlocks[b].getEndIndex() > maxJournalEnd) && (bibRef.wordBlocks[lJopBlockIndex].getStartIndex() < maxJournalEnd))
						continue;
					if (!bibRef.wordBlocks[b].firstValue().matches("[A-Z].*"))
						continue;
					if (this.hasCapWord(bibRef.wordBlocks[b])) {
						lJopBlockIndex = b;
						if (DEBUG) System.out.println(" - latest possible JoP start: '" + bibRef.wordBlocks[lJopBlockIndex].getValue() + "'");
						break;
					}
				}
				if (DEBUG) System.out.println(" - got initial JoP start: '" + bibRef.wordBlocks[lJopBlockIndex].getValue() + "'");
				
				//	if we have a primary separator, use it
				boolean gotSeparatorStart = false;
				if (tJopSeparatorTokens != null) {
					if (DEBUG) System.out.println(" - seeking backward for JoP with T-JoP separator");
					for (int b = lJopBlockIndex; b >= 1; b--) {
						if ((b != lJopBlockIndex) && !canMergeWithSuccessor[b]) {
							if (DEBUG) System.out.println(" - giving up at unattachable block: '" + bibRef.wordBlocks[b].getValue() + "'");
							break;
						}
						if (bibRef.wordBlocks[b].getStartIndex() < Math.max(minJournalStart, minPublisherStart)) {
							if (DEBUG) System.out.println(" - giving up at block starting before " + Math.max(minJournalStart, minPublisherStart) + ": '" + bibRef.wordBlocks[b].getValue() + "'");
							break;
						}
						if (!bibRef.wordBlocks[b].firstValue().matches("[A-Z].*")) {
							if (DEBUG) System.out.println(" - cannot start JoP with '" + bibRef.wordBlocks[b].firstValue() + "'");
							continue;
						}
						if (TokenSequenceUtils.indexOf(bibRef.annotation, tJopSeparatorTokens, bibRef.wordBlocks[b-1].getEndIndex()) < bibRef.wordBlocks[b].getStartIndex()) {
							lJopBlockIndex = b;
							gotSeparatorStart = true;
							if (DEBUG) System.out.println(" - latest possible JoP with T-JoP separator: '" + bibRef.wordBlocks[lJopBlockIndex].getValue() + "'");
							break;
						}
					}
				}
				
				//	if we have more occurrences of primary separator further left, use knowledge backed split scoring to extend journal/publisher
				if (DEBUG) System.out.println(" - seeking backward highest scoring split");
				float splitScore = splitAfterWordBlockScores[lJopBlockIndex-1];
				for (int b = (lJopBlockIndex-1); b >= 1; b--) {
					if (!canMergeWithSuccessor[b]) {
						if (DEBUG) System.out.println(" - giving up at unattachable block: '" + bibRef.wordBlocks[b].getValue() + "'");
						break;
					}
					if (bibRef.wordBlocks[b].getStartIndex() < Math.max(minJournalStart, minPublisherStart)) {
						if (DEBUG) System.out.println(" - giving up at block starting before " + Math.max(minJournalStart, minPublisherStart) + ": '" + bibRef.wordBlocks[b].getValue() + "'");
						break;
					}
					if (!bibRef.wordBlocks[b].firstValue().matches("[A-Z].*")) {
						if (DEBUG) System.out.println(" - cannot start JoP with '" + bibRef.wordBlocks[b].firstValue() + "'");
						continue;
					}
					if (((bibRef.wordBlocks[b].size() != 1) || !bibRef.wordBlocks[b].firstValue().matches("[A-Z][a-z]?") || bibRef.titleNumberToken[bibRef.wordBlocks[b].getStartIndex()]) && !this.hasCapWord(bibRef.wordBlocks[b])) {
						if (DEBUG) System.out.println(" - cannot start JoP without cap words");
						continue;
					}
					if (gotSeparatorStart && (tJopSeparatorTokens != null) && TokenSequenceUtils.indexOf(bibRef.annotation, tJopSeparatorTokens, bibRef.wordBlocks[b-1].getEndIndex()) != bibRef.wordBlocks[b-1].getEndIndex()) {
						if (DEBUG) System.out.println(" - cannot start JoP after non-separator");
						continue;
					}
					if (splitScore < splitAfterWordBlockScores[b-1]) {
						lJopBlockIndex = b;
						splitScore = splitAfterWordBlockScores[b-1];
						if (DEBUG) System.out.println("   --> new top scoring JoP start (" + splitAfterWordBlockScores[b-1] + "): '" + bibRef.wordBlocks[lJopBlockIndex].getValue() + "'");
					}
				}
				
				//	rule: if journal/publisher can start in second block the earliest, we're done
				//		  + make sure not to span journal/publisher over volume number and pagination
				//		  + if we have no journal/publisher at all (all candidate blocks after stray number mistaken for part designator), use part after
				for (int b = 0; b < bibRef.wordBlocks.length; b++) {
					if ((bibRef.bookContentInfos.size() != 0) && (bibRef.wordBlocks[b].getEndIndex() > maxPublisherEnd) && (bibRef.wordBlocks[lJopBlockIndex].getStartIndex() < maxPublisherEnd))
						continue;
					if ((partDesCount != 0) && (bibRef.wordBlocks[b].getEndIndex() > maxJournalEnd) && (bibRef.wordBlocks[lJopBlockIndex].getStartIndex() < maxJournalEnd))
						continue;
					if (b < lJopBlockIndex)
						wordBlockMeanings[b] = TITLE_ANNOTATION_TYPE;
					else wordBlockMeanings[b] = JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE;
				}
			}
		}
		
		//	got volume reference
		else {
			if (DEBUG) System.out.println(" - volume reference given");
			
			//	rule: block before volume ref ==> title
			for (int b = 0; b < bibRef.wordBlocks.length; b++) {
				if (bibRef.wordBlocks[b].getEndIndex() <= bibRef.volumeRef.annotation.getStartIndex())
					wordBlockMeanings[b] = TITLE_ANNOTATION_TYPE;
				else break;
			}
			
			//	handle word blocks inside volume reference
			ArrayList vrWordBlockList = new ArrayList();
			int firstVrBlockIndex = 0;
			int lastVrBlockIndex = 0;
			for (int b = 0; b < bibRef.wordBlocks.length; b++) {
				if (bibRef.wordBlocks[b].getEndIndex() <= bibRef.volumeRef.annotation.getStartIndex())
					continue;
				else if (bibRef.wordBlocks[b].getEndIndex() <= bibRef.volumeRef.annotation.getEndIndex()) {
					if (vrWordBlockList.isEmpty())
						firstVrBlockIndex = b;
					lastVrBlockIndex = b;
					vrWordBlockList.add(bibRef.wordBlocks[b]);
				}
				else break;
			}
			
			//	restrict JoP start to end of proceedings titel if latter given, and make everything before volume title
			if (proceedingsTitles.length != 0) {
				minJournalStart = proceedingsTitles[proceedingsTitles.length-1].getEndIndex();
				minPublisherStart = proceedingsTitles[proceedingsTitles.length-1].getEndIndex();
			}
			
			//	restrict to earliest known JoP with separator punctuation before it if latter given
			else if ((knownJops.length != 0) && (tJopSeparatorTokens != null)) {
				for (int j = 0; j < knownJops.length; j++) {
					if (knownJops[j].getStartIndex() < tJopSeparatorTokens.size())
						continue;
					if (!AnnotationUtils.liesIn(knownJops[j], bibRef.volumeReference))
						continue;
					if (TokenSequenceUtils.indexOf(bibRef.annotation, tJopSeparatorTokens, (knownJops[j].getStartIndex() - tJopSeparatorTokens.size())) == (knownJops[j].getStartIndex() - tJopSeparatorTokens.size())) {
						minJournalStart = knownJops[j].getStartIndex();
						minPublisherStart = knownJops[j].getStartIndex();
						break;
					}
				}
			}
			
			//	rule: first block in volume ref ==> volume title
			wordBlockMeanings[firstVrBlockIndex] = VOLUME_TITLE_ANNOTATION_TYPE;
			
			//	rule: rare as it may be, but if we have only a web site volume title (singe page cited, etc.), just use it as is
			if (isWebSiteTitle[lastVrBlockIndex]) {
				if (DEBUG) System.out.println(" - got web site volume title: '" + TokenSequenceUtils.concatTokens(bibRef.annotation, bibRef.wordBlocks[firstVrBlockIndex].getStartIndex(), (bibRef.wordBlocks[lastVrBlockIndex].getEndIndex() - bibRef.wordBlocks[firstVrBlockIndex].getStartIndex())) + "'");
				Arrays.fill(wordBlockMeanings, firstVrBlockIndex, lastVrBlockIndex, TITLE_ANNOTATION_TYPE);
			}
			
			//	find last possible start of journal/publisher
			int lJopBlockIndex = (isWebSiteTitle[lastVrBlockIndex] ? (lastVrBlockIndex+1) : (firstVrBlockIndex+1));
			if (DEBUG && (lJopBlockIndex < bibRef.wordBlocks.length))
				System.out.println(" - got initial JoP start: '" + bibRef.wordBlocks[lJopBlockIndex].getValue() + "'");
			
			//	rule: last capitalized block preceding part designator ==> latest start for journal/publisher
			if (DEBUG) System.out.println(" - seeking latest possible JoP start");
			for (int b = lastVrBlockIndex; b >= (firstVrBlockIndex+1); b--) {
				if (bibRef.wordBlocks[b].getStartIndex() < Math.max(minJournalStart, minPublisherStart)) {
					if (DEBUG) System.out.println(" - giving up at block starting before " + Math.max(minJournalStart, minPublisherStart) + ": '" + bibRef.wordBlocks[b].getValue() + "'");
					break;
				}
				if ((bibRef.bookContentInfos.size() != 0) && (bibRef.wordBlocks[b].getEndIndex() > maxPublisherEnd) && (lJopBlockIndex < bibRef.wordBlocks.length) && (bibRef.wordBlocks[lJopBlockIndex].getStartIndex() < maxPublisherEnd))
					continue;
				if ((partDesCount != 0) && (bibRef.wordBlocks[b].getEndIndex() > maxJournalEnd) && (lJopBlockIndex < bibRef.wordBlocks.length) && (bibRef.wordBlocks[lJopBlockIndex].getStartIndex() < maxJournalEnd))
					continue;
				if (!bibRef.wordBlocks[b].firstValue().matches("[A-Z].*"))
					continue;
				if (this.hasCapWord(bibRef.wordBlocks[b])) {
					lJopBlockIndex = b;
					if (DEBUG) System.out.println(" - latest possible JoP start: '" + bibRef.wordBlocks[lJopBlockIndex].getValue() + "'");
					break;
				}
			}
			
			//	if we have a primary separator, use it
			boolean gotSeparatorStart = false;
			if (tJopSeparatorTokens != null) {
				if (DEBUG) System.out.println(" - seeking backward for JoP with T-JoP separator '" + tJopSeparator + "'");
				for (int b = lJopBlockIndex; b >= (firstVrBlockIndex+1); b--) {
					if (b >= bibRef.wordBlocks.length)
						continue; // we need this catch here in case separator doesn't occur at all and bounds reach beyond array size
					if ((b != lJopBlockIndex) && !canMergeWithSuccessor[b]) {
						if (DEBUG) System.out.println(" - giving up at unattachable block: '" + bibRef.wordBlocks[b].getValue() + "'");
						break;
					}
					if (bibRef.wordBlocks[b].getStartIndex() < Math.max(minJournalStart, minPublisherStart)) {
						if (DEBUG) System.out.println(" - giving up at block starting before " + Math.max(minJournalStart, minPublisherStart) + ": '" + bibRef.wordBlocks[b].getValue() + "'");
						break;
					}
					if (!bibRef.wordBlocks[b].firstValue().matches("[A-Z].*")) {
						if (DEBUG) System.out.println(" - cannot start JoP with '" + bibRef.wordBlocks[b].firstValue() + "'");
						continue;
					}
					if (TokenSequenceUtils.indexOf(bibRef.annotation, tJopSeparatorTokens, bibRef.wordBlocks[b-1].getEndIndex()) == bibRef.wordBlocks[b-1].getEndIndex()) {
						lJopBlockIndex = b;
						gotSeparatorStart = true;
						if (DEBUG) System.out.println(" - latest possible JoP with T-JoP separator: '" + bibRef.wordBlocks[lJopBlockIndex].getValue() + "'");
						break;
					}
				}
			}
			
			//	if we have more occurrences of primary separator further left, use knowledge backed split scoring to extend journal/publisher
			if (DEBUG) System.out.println(" - seeking backward highest scoring split");
			float splitScore = splitAfterWordBlockScores[lJopBlockIndex-1];
			for (int b = (lJopBlockIndex-1); b >= (firstVrBlockIndex+1); b--) {
				if (!canMergeWithSuccessor[b]) {
					if (DEBUG) System.out.println(" - giving up at unattachable block: '" + bibRef.wordBlocks[b].getValue() + "'");
					break;
				}
				if (bibRef.wordBlocks[b].getStartIndex() < Math.max(minJournalStart, minPublisherStart)) {
					if (DEBUG) System.out.println(" - giving up at block starting before " + Math.max(minJournalStart, minPublisherStart) + ": '" + bibRef.wordBlocks[b].getValue() + "'");
					break;
				}
				if (!bibRef.wordBlocks[b].firstValue().matches("[A-Z].*")) {
					if (DEBUG) System.out.println(" - cannot start JoP with '" + bibRef.wordBlocks[b].firstValue() + "'");
					continue;
				}
				if (((bibRef.wordBlocks[b].size() != 1) || !bibRef.wordBlocks[b].firstValue().matches("[A-Z][a-z]?") || bibRef.titleNumberToken[bibRef.wordBlocks[b].getStartIndex()]) && !this.hasCapWord(bibRef.wordBlocks[b])) {
					if (DEBUG) System.out.println(" - cannot start JoP without cap words");
					continue;
				}
				if (gotSeparatorStart && (tJopSeparatorTokens != null) && TokenSequenceUtils.indexOf(bibRef.annotation, tJopSeparatorTokens, bibRef.wordBlocks[b-1].getEndIndex()) != bibRef.wordBlocks[b-1].getEndIndex()) {
					if (DEBUG) System.out.println(" - cannot start JoP after non-separator");
					continue;
				}
				if (splitScore < splitAfterWordBlockScores[b-1]) {
					lJopBlockIndex = b;
					splitScore = splitAfterWordBlockScores[b-1];
					if (DEBUG) System.out.println(" - new top scoring JoP start (" + splitAfterWordBlockScores[b-1] + "): '" + bibRef.wordBlocks[lJopBlockIndex].getValue() + "'");
				}
			}
			
			//	rule: if journal/publisher can start in second block the earliest, we're done
			//		  + make sure not to span journal/publisher over volume number and pagination
			for (int b = firstVrBlockIndex; b <= lastVrBlockIndex; b++) {
				if ((bibRef.bookContentInfos.size() != 0) && (bibRef.wordBlocks[b].getEndIndex() > maxPublisherEnd))
					continue;
				if ((partDesCount != 0) && (bibRef.wordBlocks[b].getEndIndex() > maxJournalEnd))
					continue;
				if (b < lJopBlockIndex)
					wordBlockMeanings[b] = VOLUME_TITLE_ANNOTATION_TYPE;
				else wordBlockMeanings[b] = JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE;
			}
			
			//	go looking for possible publishers after pagination
			for (int b = (lastVrBlockIndex+1); b < bibRef.wordBlocks.length; b++)
				wordBlockMeanings[b] = JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE;
		}
		
		if (DEBUG) {
			System.out.println("Word blocks classified:");
			for (int b = 0; b < bibRef.wordBlocks.length; b++)
				System.out.println(" - " + wordBlockMeanings[b] + ": " + bibRef.wordBlocks[b].getValue());
		}
		
		//	annotate what we have, and deal with multiple titles and journals/publishers
		int start = -1;
		float scoreSum = 0;
		ArrayList titles = new ArrayList(2);
		ArrayList volumeTitles = new ArrayList(2);
		ArrayList jops = new ArrayList(2);
		for (int b = 0; b < bibRef.wordBlocks.length; b++) {
			if (wordBlockMeanings[b] == null)
				continue;
			if (start == -1)
				start = bibRef.wordBlocks[b].getStartIndex();
			scoreSum += wordBlockScores[b];
			if (canMergeWithSuccessor[b] && ((b+1) < bibRef.wordBlocks.length) && wordBlockMeanings[b].equals(wordBlockMeanings[b+1]))
				continue;
			Annotation typeAnnot = Gamta.newAnnotation(bibRef.annotation, wordBlockMeanings[b], start, (bibRef.wordBlocks[b].getEndIndex() - start));
//			if (TITLE_ANNOTATION_TYPE.equals(wordBlockMeanings[b]) && (bibRef.title == null))
//				bibRef.title = typeAnnot;
			if (TITLE_ANNOTATION_TYPE.equals(wordBlockMeanings[b]) && (bibRef.title == null))
				titles.add(typeAnnot);
//			else if (VOLUME_TITLE_ANNOTATION_TYPE.equals(wordBlockMeanings[b]) && (bibRef.volumeTitle == null))
//				bibRef.volumeTitle = typeAnnot;
			else if (VOLUME_TITLE_ANNOTATION_TYPE.equals(wordBlockMeanings[b]) && (bibRef.volumeTitle == null))
				volumeTitles.add(typeAnnot);
//			else if (JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE.equals(wordBlockMeanings[b]) && (bibRef.journalOrPublisher == null))
//				bibRef.journalOrPublisher = typeAnnot;
			else if (JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE.equals(wordBlockMeanings[b]) && (bibRef.journalOrPublisher == null))
				jops.add(typeAnnot);
			typeAnnot.setAttribute("jopScore", ("" + scoreSum));
			scoreSum = 0;
			if (DEBUG) System.out.println(" - " + typeAnnot.toXML());
			start = -1;
		}
		
		//	handle multiple titles if present
		if (titles.size() == 1)
			bibRef.title = ((Annotation) titles.remove(0));
		else if (titles.size() != 0) {
			if (DEBUG) System.out.println("Picking title from " + titles.size() + " candidates:");
			
			//	compare to element order in other references
			for (int t = 0; t < titles.size(); t++)
				this.assessSurroundingTypes(bibRef, ((Annotation) titles.get(t)), bibRefs);
			
			//	handle titles assigned to other types
			this.assignTypedWordBlocks(bibRef, titles);
			
			//	select highest scoring title, or assign to other element
			bibRef.title = this.findBestUntypedWordBlock(titles, false);
			
			//	remove selected title from lingering ones
			for (int t = 0; t < titles.size(); t++) {
				if (titles.get(t) == bibRef.title)
					titles.remove(t--);
			}
		}
		
		//	handle multiple volume titles if present
		if (volumeTitles.size() != 0)
			bibRef.volumeTitle = ((Annotation) volumeTitles.remove(0));
		
		//	two candidate volume titles, but no journal/publisher, recycle remaining volume title
		if ((jops.size() == 0) && (volumeTitles.size() != 0)) {
			jops.addAll(volumeTitles);
			volumeTitles.clear();
			if (DEBUG) System.out.println("Re-purposed remaining volume titles as journal/publisher candidates for lack of alternatives");
		}
		
		//	two candidate titles, but no journal/publisher, recycle remaining title
		if ((jops.size() == 0) && (titles.size() != 0)) {
			jops.addAll(titles);
			titles.clear();
			if (DEBUG) System.out.println("Re-purposed remaining titles as journal/publisher candidates for lack of alternatives");
		}
		
		//	handle multiple journals/publishers if present
		if (jops.size() == 1)
			bibRef.journalOrPublisher = ((Annotation) jops.remove(0));
		else if (jops.size() != 0) {
			if (DEBUG) System.out.println("Picking journal/publisher from " + jops.size() + " candidates:");
			
			//	compare to element order in other references
			for (int j = 0; j < jops.size(); j++) {
				Annotation jop = ((Annotation) jops.get(j));
				this.assessSurroundingTypes(bibRef, jop, bibRefs);
				//	TODO also consider word block score
				
				//	TODO insist on capitalized word
				
				//	TODO also use 'knownJoP' markers
			}
			
			//	handle titles assigned to other types
			this.assignTypedWordBlocks(bibRef, jops);
			
			//	select highest scoring journal/publisher, or assign to other element
			bibRef.journalOrPublisher = this.findBestUntypedWordBlock(jops, true);
			
			//	remove selected journal/publisher from lingering ones
			for (int j = 0; j < jops.size(); j++) {
				if (jops.get(j) == bibRef.journalOrPublisher)
					jops.remove(j--);
			}
		}
		
		//	if non-selected title adjacent to JoP, merge the two
		if (titles.size() != 0) {
			if (DEBUG) System.out.println("Handling remaining candidate titles:");
			if (bibRef.journalOrPublisher == null) {
				bibRef.journalOrPublisher = ((Annotation) titles.remove(0));
				if (DEBUG) System.out.println(" - " + bibRef.journalOrPublisher.toXML());
				if (DEBUG) System.out.println(" ==> filled in for lacking journal/publisher: " + bibRef.journalOrPublisher.toXML());
			}
			for (int t = (titles.size() - 1); t >= 0; t--) {
				Annotation title = ((Annotation) titles.get(t));
				if (DEBUG) System.out.println(" - " + title.toXML());
				if (!title.firstValue().matches("[A-Z].*")) {
					if (DEBUG) System.out.println(" --> cannot attach, lower case start");
					continue;
				}
				if (bibRef.journalOrPublisher.getStartIndex() < title.getEndIndex()) {
					if (DEBUG) System.out.println(" --> cannot attach, too late in reference");
					continue;
				}
				boolean canMerge = true;
				for (int b = title.getEndIndex(); b < bibRef.journalOrPublisher.getStartIndex(); b++)
					if (!"_".equals(bibRef.structure.details[b]) && !Gamta.isPunctuation(bibRef.annotation.valueAt(b))) {
						canMerge = false;
						if (DEBUG) System.out.println(" --> cannot attach due to intermediate " + bibRef.structure.details[b] + ": " + bibRef.annotation.valueAt(b));
						break;
					}
				if (canMerge) {
					Annotation jop = Gamta.newAnnotation(bibRef.annotation, JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE, title.getStartIndex(), (bibRef.journalOrPublisher.getEndIndex() - title.getStartIndex()));
					jop.copyAttributes(bibRef.journalOrPublisher);
					bibRef.journalOrPublisher = jop;
					if (DEBUG) System.out.println(" ==> attached to journal/publisher: " + bibRef.journalOrPublisher.toXML());
				}
			}
		}
		
		//	if non-selected volume title adjacent to JoP, merge the two
		if (volumeTitles.size() != 0) {
			if (DEBUG) System.out.println("Handling remaining candidate volume titles:");
			if (bibRef.journalOrPublisher == null) {
				bibRef.journalOrPublisher = ((Annotation) volumeTitles.remove(0));
				if (DEBUG) System.out.println(" - " + bibRef.journalOrPublisher.toXML());
				if (DEBUG) System.out.println(" ==> filled in for lacking journal/publisher: " + bibRef.journalOrPublisher.toXML());
			}
			for (int t = (volumeTitles.size() - 1); t >= 0; t--) {
				Annotation volumeTitle = ((Annotation) volumeTitles.get(t));
				if (DEBUG) System.out.println(" - " + volumeTitle.toXML());
				if (!volumeTitle.firstValue().matches("[A-Z].*")) {
					if (DEBUG) System.out.println(" --> cannot attach, lower case start");
					continue;
				}
				if (bibRef.journalOrPublisher.getStartIndex() < volumeTitle.getEndIndex()) {
					if (DEBUG) System.out.println(" --> cannot attach, too late in reference");
					continue;
				}
				boolean canMerge = true;
				for (int b = volumeTitle.getEndIndex(); b < bibRef.journalOrPublisher.getStartIndex(); b++)
					if (!"_".equals(bibRef.structure.details[b]) && !Gamta.isPunctuation(bibRef.annotation.valueAt(b))) {
						canMerge = false;
						if (DEBUG) System.out.println(" --> cannot attach due to intermediate " + bibRef.structure.details[b] + ": " + bibRef.annotation.valueAt(b));
						break;
					}
				if (canMerge) {
					Annotation jop = Gamta.newAnnotation(bibRef.annotation, JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE, volumeTitle.getStartIndex(), (bibRef.journalOrPublisher.getEndIndex() - volumeTitle.getStartIndex()));
					jop.copyAttributes(bibRef.journalOrPublisher);
					bibRef.journalOrPublisher = jop;
					if (DEBUG) System.out.println(" ==> attached to journal/publisher: " + bibRef.journalOrPublisher.toXML());
				}
			}
		}
		
		//	if non-selected JoP adjacent to title or volume title, merge the two
		if (jops.size() != 0) {
			if (DEBUG) System.out.println("Handling remaining candidate journals/publishers:");
			for (int j = 0; j < jops.size(); j++) {
				Annotation jop = ((Annotation) jops.get(j));
				if (DEBUG) System.out.println(" - " + jop.toXML());
				if (!jop.firstValue().matches("[A-Z].*")) {
					if (DEBUG) System.out.println(" --> cannot attach, lower case start");
					continue;
				}
				if (bibRef.journalOrPublisher == null) {
					bibRef.journalOrPublisher = jop;
					if (DEBUG) System.out.println(" ==> filled in for lacking journal/publisher: " + bibRef.journalOrPublisher.toXML());
					continue;
				}
				if (bibRef.journalOrPublisher.getStartIndex() < jop.getEndIndex()) {
					if (DEBUG) System.out.println(" --> cannot attach, too late in reference");
					continue;
				}
				
				//	try and attach to title if given
				if ((bibRef.title != null) && (bibRef.title.getEndIndex() <= jop.getStartIndex())) {
					boolean canMerge = true;
					for (int b = bibRef.title.getEndIndex(); b < jop.getStartIndex(); b++)
						if (!"_".equals(bibRef.structure.details[b]) && !Gamta.isPunctuation(bibRef.annotation.valueAt(b))) {
							canMerge = false;
							if (DEBUG) System.out.println(" --> cannot attach to title due to intermediate " + bibRef.structure.details[b] + ": " + bibRef.annotation.valueAt(b));
							break;
						}
					if (canMerge) {
						Annotation title = Gamta.newAnnotation(bibRef.annotation, TITLE_ANNOTATION_TYPE, bibRef.title.getStartIndex(), (jop.getEndIndex() - bibRef.title.getStartIndex()));
						title.copyAttributes(bibRef.title);
						bibRef.title = title;
						if (DEBUG) System.out.println(" ==> attached to title: " + bibRef.title.toXML());
						continue;
					}
				}
				
				//	try and attach to volume title if given
				if ((bibRef.volumeTitle != null) && (bibRef.volumeTitle.getEndIndex() <= jop.getStartIndex())) {
					boolean canMerge = true;
					for (int b = bibRef.volumeTitle.getEndIndex(); b < jop.getStartIndex(); b++)
						if (!"_".equals(bibRef.structure.details[b]) && !Gamta.isPunctuation(bibRef.annotation.valueAt(b))) {
							canMerge = false;
							if (DEBUG) System.out.println(" --> cannot attach to volume title due to intermediate " + bibRef.structure.details[b] + ": " + bibRef.annotation.valueAt(b));
							break;
						}
					if (canMerge) {
						Annotation volumeTitle = Gamta.newAnnotation(bibRef.annotation, VOLUME_TITLE_ANNOTATION_TYPE, bibRef.volumeTitle.getStartIndex(), (jop.getEndIndex() - bibRef.volumeTitle.getStartIndex()));
						volumeTitle.copyAttributes(bibRef.volumeTitle);
						bibRef.volumeTitle = volumeTitle;
						if (DEBUG) System.out.println(" ==> attached to volume title: " + bibRef.volumeTitle.toXML());
						continue;
					}
				}
			}
		}
	}
	
	private void assessSurroundingTypes(BibRef bibRef, Annotation wordBlock, BibRef[] bibRefs) {
		
		//	TODO also consider word block score
		
		//	TODO also use 'knownJoP' markers
		
		String beforeType = "|";
		String afterType = "|";
		CountingSet types = new CountingSet();
		if (DEBUG) System.out.println(" - investigating '" + wordBlock.getValue() + "'");
		for (int b = (wordBlock.getStartIndex()-1); b >= 0; b--)
			if (!"_".equals(bibRef.structure.details[b])) {
				beforeType = bibRef.structure.details[b];
				if (DEBUG) System.out.println("   - before type is " + beforeType);
				break;
			}
		for (int a = wordBlock.getEndIndex(); a < bibRef.annotation.size(); a++)
			if (!"_".equals(bibRef.structure.details[a])) {
				afterType = bibRef.structure.details[a];
				if (DEBUG) System.out.println("   - after type is " + afterType);
				break;
			}
		for (int s = 0; s < bibRefs.length; s++) {
			if (bibRefs[s] == bibRef)
				continue;
			for (int i = 0; i < bibRefs[s].structure.punctSummary.length; i++) {
				if (beforeType.equals(bibRefs[s].structure.punctSummary[i])) {
					for (int a = (i+1); a < bibRefs[s].structure.punctSummary.length; a++)
						if ("_".equals(bibRefs[s].structure.punctSummary[a]) || !Gamta.isPunctuation(bibRefs[s].structure.punctSummary[a])) {
							types.add(bibRefs[s].structure.punctSummary[a]);
							break;
						}
				}
				if (afterType.equals(bibRefs[s].structure.punctSummary[i])) {
					for (int b = (i-1); b >= 0; b--)
						if ("_".equals(bibRefs[s].structure.punctSummary[b]) || !Gamta.isPunctuation(bibRefs[s].structure.punctSummary[b])) {
							types.add(bibRefs[s].structure.punctSummary[b]);
							break;
						}
				}
			}
		}
		if (DEBUG) System.out.println(" - types after " + beforeType + " / before " + afterType + ":");
		int inferredTypeScore = 0;
		for (Iterator tit = types.iterator(); tit.hasNext();) {
			String type = ((String) tit.next());
			int typeScore = types.getCount(type);
			if (DEBUG) System.out.println("   - " + type + " " + typeScore);
			if (typeScore > inferredTypeScore) {
				wordBlock.setAttribute(TYPE_ATTRIBUTE, type);
				wordBlock.setAttribute((TYPE_ATTRIBUTE + "Score"), ("" + typeScore));
				inferredTypeScore = typeScore;
				if (DEBUG) System.out.println("     ==> new top type");
			}
		}
	}
	
	private void assignTypedWordBlocks(BibRef bibRef, ArrayList wordBlocks) {
		for (int w = 0; w < wordBlocks.size(); w++) {
			Annotation wordBlock = ((Annotation) wordBlocks.get(w));
			if (AUTHOR_LIST_ANNOTATION_TYPE.equals(wordBlock.getAttribute(TYPE_ATTRIBUTE)) && (bibRef.authorList == null)) {
				bibRef.authors = new Annotation[1];
				bibRef.authors[0] = Gamta.newAnnotation(bibRef.annotation, AUTHOR_ANNOTATION_TYPE, wordBlock.getStartIndex(), wordBlock.size());
				wordBlocks.remove(w--);
			}
			else if (EDITOR_LIST_ANNOTATION_TYPE.equals(wordBlock.getAttribute(TYPE_ATTRIBUTE))) {
				bibRef.editors = new Annotation[1];
				bibRef.editors[0] = Gamta.newAnnotation(bibRef.annotation, EDITOR_ANNOTATION_TYPE, wordBlock.getStartIndex(), wordBlock.size());
				wordBlocks.remove(w--);
			}
		}
	}
	
	private Annotation findBestUntypedWordBlock(ArrayList wordBlocks, boolean isJoP) {
		int maxScore = -1;
		Annotation maxScoreWordBlock = null;
		
		//	find highest scoring unassigned word block, and 
		for (int w = 0; w < wordBlocks.size(); w++) {
			Annotation wordBlock = ((Annotation) wordBlocks.get(w));
			if (!"_".equals(wordBlock.getAttribute(TYPE_ATTRIBUTE)))
				continue;
			int score = Integer.parseInt((String) wordBlock.getAttribute((TYPE_ATTRIBUTE + "Score"), "0"));
			if (maxScore < score) {
				maxScoreWordBlock = wordBlock;
				maxScore = score;
			}
		}
		
		//	finally
		return maxScoreWordBlock;
	}
	
	private Annotation includeTailingPunctuation(BibRef bibRef, Annotation wordBlock, String includePunctuation) {
		if (wordBlock == null)
			return wordBlock;
		if (wordBlock.getEndIndex() == bibRef.annotation.size())
			return wordBlock;
		if (!"_".equals(bibRef.structure.details[wordBlock.getEndIndex()]))
			return wordBlock;
		String tailingToken = bibRef.annotation.valueAt(wordBlock.getEndIndex());
		if ((tailingToken.length() > 1) || (includePunctuation.indexOf(tailingToken) == -1))
			return wordBlock;
		Annotation eWordBlock;
		if (wordBlock instanceof StandaloneAnnotation) {
			eWordBlock = Gamta.newAnnotation(bibRef.annotation, wordBlock.getType(), wordBlock.getStartIndex(), (wordBlock.size() + 1));
			eWordBlock.copyAttributes(wordBlock);
		}
		else {
			eWordBlock = bibRef.annotation.addAnnotation(wordBlock.getType(), wordBlock.getStartIndex(), (wordBlock.size() + 1));
			eWordBlock.copyAttributes(wordBlock);
			bibRef.annotation.removeAnnotation(wordBlock);
		}
		return eWordBlock;
	}
	
	private Annotation removeTailingPunctuation(BibRef bibRef, Annotation wordBlock, String retainPunctuation) {
		if (wordBlock == null)
			return wordBlock;
		if (wordBlock.size() == 1)
			return wordBlock;
		String tailingToken = wordBlock.lastValue();
		if ((tailingToken.length() > 1) || !Gamta.isPunctuation(tailingToken) || (retainPunctuation.indexOf(tailingToken) != -1))
			return wordBlock;
		Annotation tWordBlock;
		if (wordBlock instanceof StandaloneAnnotation) {
			tWordBlock = Gamta.newAnnotation(bibRef.annotation, wordBlock.getType(), wordBlock.getStartIndex(), (wordBlock.size() - 1));
			tWordBlock.copyAttributes(wordBlock);
		}
		else {
			tWordBlock = bibRef.annotation.addAnnotation(wordBlock.getType(), wordBlock.getStartIndex(), (wordBlock.size() - 1));
			tWordBlock.copyAttributes(wordBlock);
			bibRef.annotation.removeAnnotation(wordBlock);
		}
		return tWordBlock;
	}
	
	private void parseOrigin(BibRef bibRef, String primarySeparator) {
		if (bibRef.type == null)
			return;
		if (bibRef.journalOrPublisher == null) {
			System.out.println("MISSING ORIGIN IN " + bibRef.annotation.toXML());
			return;
		}
		if (bibRef.preExistingStructure) {
			if (bibRef.type.name.startsWith("journal") && (bibRef.journal != null))
				return;
			else if (bibRef.type.name.startsWith("book") && ((bibRef.publisher != null) || (bibRef.location != null)))
				return;
			else if (bibRef.type.name.startsWith("proceedings") && (bibRef.proceedingsVolumeTitle != null))
				return;
		}
		
		if (bibRef.type.name.startsWith("journal")) {
			bibRef.journal = Gamta.newAnnotation(bibRef.annotation, bibRef.journalOrPublisher);
			bibRef.journal.changeTypeTo(JOURNAL_NAME_ANNOTATION_TYPE);
			return;
		}
		
		if (bibRef.type.name.startsWith("book")) {
			if (!this.parsePublisher(bibRef, bibRef.journalOrPublisher)) {
				//	TODO use lexicons to determine if publisher or location
				//	TODO alternatively, also use number of words (single words become locations)
				bibRef.publisher = Gamta.newAnnotation(bibRef.annotation, bibRef.journalOrPublisher);
				bibRef.publisher.changeTypeTo(PUBLISHER_ANNOTATION_TYPE);
			}
			return;
		}
		
		if (bibRef.type.name.startsWith("proceedings")) {
			//	chunk off volume title, and split rest with publisher parsing heuristics
			int vtSize = 0;
			while ((vtSize < bibRef.journalOrPublisher.size())) {
				String vtValue = bibRef.journalOrPublisher.valueAt(vtSize);
				if (".".equals(vtValue) && !".".equals(primarySeparator)) {
					vtSize++;
					continue;
				}
				if (",.;:".indexOf(vtValue) == -1)
					vtSize++;
				else break;
			}
			if (vtSize < bibRef.journalOrPublisher.size()) {
				bibRef.proceedingsVolumeTitle = Gamta.newAnnotation(bibRef.annotation, PUBLISHER_ANNOTATION_TYPE, bibRef.journalOrPublisher.getStartIndex(), vtSize);
				Annotation location = Gamta.newAnnotation(bibRef.annotation, LOCATION_ANNOTATION_TYPE, (bibRef.journalOrPublisher.getStartIndex() + vtSize + 1), (bibRef.journalOrPublisher.size() - vtSize - 1));
				if (!this.parsePublisher(bibRef, location))
					bibRef.location = location;
			}
			else {
				bibRef.proceedingsVolumeTitle = Gamta.newAnnotation(bibRef.annotation, bibRef.journalOrPublisher);
				bibRef.proceedingsVolumeTitle.changeTypeTo(VOLUME_TITLE_ANNOTATION_TYPE);
			}
			return;
		}
	}
	
	private boolean parsePublisher(BibRef bibRef, Annotation publisher) {
		int split = TokenSequenceUtils.indexOf(bibRef.journalOrPublisher, ":");
		if (split == -1)
			split = TokenSequenceUtils.indexOf(bibRef.journalOrPublisher, ",");
		if (split == -1)
			return false;
		if (":".equals(bibRef.journalOrPublisher.valueAt(split))) {
			bibRef.publisher = Gamta.newAnnotation(bibRef.annotation, PUBLISHER_ANNOTATION_TYPE, (bibRef.journalOrPublisher.getStartIndex() + split + 1), (bibRef.journalOrPublisher.size() - split - 1));
			bibRef.location = Gamta.newAnnotation(bibRef.annotation, LOCATION_ANNOTATION_TYPE, bibRef.journalOrPublisher.getStartIndex(), split);
		}
		else {
			bibRef.publisher = Gamta.newAnnotation(bibRef.annotation, PUBLISHER_ANNOTATION_TYPE, bibRef.journalOrPublisher.getStartIndex(), split);
			bibRef.location = Gamta.newAnnotation(bibRef.annotation, LOCATION_ANNOTATION_TYPE, (bibRef.journalOrPublisher.getStartIndex() + split + 1), (bibRef.journalOrPublisher.size() - split - 1));
		}
		return true;
	}
	
	private void annotateDetails(BibRef bibRef) {
		
		//	truncate and unify page data
		if (bibRef.pagination != null) {
			int start = bibRef.pagination.getStartIndex();
			while ((start < bibRef.pagination.getEndIndex()) && !Gamta.isNumber(bibRef.annotation.valueAt(start)))
				start++;
			if ((start != bibRef.pagination.getStartIndex()) && (start < bibRef.pagination.getEndIndex()))
				bibRef.pagination = Gamta.newAnnotation(bibRef.annotation, bibRef.pagination.getType(), start, (bibRef.pagination.getEndIndex() - start));
			bibRef.pagination.setAttribute(TYPE_ATTRIBUTE, bibRef.pagination.getType());
			bibRef.pagination.changeTypeTo(PAGINATION_ANNOTATION_TYPE);
		}
		
		//	add annotations
		if (bibRef.authors != null)
			for (int a = 0; a < bibRef.authors.length; a++)
				bibRef.annotation.addAnnotation(bibRef.authors[a]);
		if (bibRef.editors != null)
			for (int e = 0; e < bibRef.editors.length; e++)
				bibRef.annotation.addAnnotation(bibRef.editors[e]);
		if (bibRef.year != null)
			bibRef.annotation.addAnnotation(bibRef.year);
		if (bibRef.title != null) {
			bibRef.annotation.addAnnotation(bibRef.title);
		}
		
		//	handle volume reference details in an integrated manner
		if (bibRef.volumeDesignator != null)
			bibRef.annotation.addAnnotation(bibRef.volumeDesignator);
		if (bibRef.issueDesignator != null)
			bibRef.annotation.addAnnotation(bibRef.issueDesignator);
		if (bibRef.numberDesignator != null)
			bibRef.annotation.addAnnotation(bibRef.numberDesignator);
		
		if (bibRef.volumeTitle != null)
			bibRef.annotation.addAnnotation(bibRef.volumeTitle);
		if (bibRef.journalOrPublisher != null)
			bibRef.annotation.addAnnotation(bibRef.journalOrPublisher);
		
		if (bibRef.pagination != null)
			bibRef.annotation.addAnnotation(bibRef.pagination);
		
		//	set type attribute here
		if (bibRef.type != null)
			bibRef.annotation.setAttribute(PUBLICATION_TYPE_ATTRIBUTE, bibRef.type.name);
		
		if (DEBUG) System.out.println("Result for reference " + bibRef.annotation.toXML());
		
		//	annotate DOIs ...
		for (int d = 0; d < bibRef.dois.length; d++) {
			if (DEBUG) System.out.println("DOI: " + bibRef.dois[d].toXML());
			bibRef.annotation.addAnnotation(PUBLICATION_DOI_ANNOTATION_TYPE, bibRef.dois[d].getStartIndex(), bibRef.dois[d].size());
		}
		
		//	 ... and URLs ...
		for (int u = 0; u < bibRef.urls.length; u++) {
			if (DEBUG) System.out.println("URL: " + bibRef.urls[u].toXML());
			bibRef.annotation.addAnnotation(PUBLICATION_URL_ANNOTATION_TYPE, bibRef.urls[u].getStartIndex(), bibRef.urls[u].size());
		}
		
		//	... including access dates ...
		if (bibRef.urlAccessDate != null)
			bibRef.annotation.addAnnotation(ACCESS_DATE_ANNOTATION_TYPE, bibRef.urlAccessDate.getStartIndex(), bibRef.urlAccessDate.size());
		
		//	... and book content info
		for (int i = 0; i < bibRef.bookContentInfos.size(); i++) {
			Annotation bci = ((Annotation) bibRef.bookContentInfos.get(i));
			if (DEBUG) System.out.println("Book Content Info: " + bci.toXML());
			bibRef.annotation.addAnnotation(BOOK_CONTENT_INFO_ANNOTATION_TYPE, bci.getStartIndex(), bci.size());
		}
		
		//	filter URLs that are also DOIs
		AnnotationFilter.removeContained(bibRef.annotation, PUBLICATION_DOI_ANNOTATION_TYPE, PUBLICATION_URL_ANNOTATION_TYPE);
		AnnotationFilter.removeContaining(bibRef.annotation, PUBLICATION_URL_ANNOTATION_TYPE, PUBLICATION_DOI_ANNOTATION_TYPE);
		
		//	print data
		if (DEBUG) {
			System.out.println("authorList: " + ((bibRef.authorList == null) ? "" : bibRef.authorList.getValue()));
			if (bibRef.authors != null)
				for (int a = 0; a < bibRef.authors.length; a++)
					System.out.println("  - " + bibRef.authors[a].getValue());
			System.out.println("year: " + ((bibRef.year == null) ? "" : bibRef.year.getValue()));
			System.out.println("title: " + ((bibRef.title == null) ? "" : bibRef.title.getValue()));
			if (bibRef.editors != null) {
				System.out.println("editorList:");
				for (int e = 0; e < bibRef.editors.length; e++)
					System.out.println("  - " + bibRef.editors[e].getValue());
			}
			System.out.println("volume title: " + ((bibRef.volumeTitle == null) ? "" : bibRef.volumeTitle.getValue()));
			System.out.println("journal/publisher: " + ((bibRef.journalOrPublisher == null) ? "" : bibRef.journalOrPublisher.getValue()));
			System.out.println("volume: " + ((bibRef.volumeDesignator == null) ? "" : bibRef.volumeDesignator.getValue()));
			System.out.println("page(s): " + ((bibRef.pagination == null) ? "" : bibRef.pagination.getValue()));
			System.out.println();
		}
	}
	
	private void classify(final BibRef bibRef) {
//		
//		if (DEBUG) System.out.println("Classifying " + bibRef.annotation.toXML());
//		String typeName = this.referenceTypeSystem.classify(new AbstractAttributed() {
//			public Object getAttribute(String name, Object def) {
//				if (TITLE_ANNOTATION_TYPE.equals(name)) {
//					return ((bibRef.title == null) ? def : bibRef.title.getValue());
//				}
//				return super.getAttribute(name, def);
//			}
//			public Object getAttribute(String name) {
//				return this.getAttribute(name, null);
//			}
//			public boolean hasAttribute(String name) {
//				return (this.getAttribute(name) != null);
//			}
//		});
//		if (DEBUG) System.out.println(" ==> classified as " + typeName);
//		bibRef.type = ((BibRefType) this.referenceTypes.get(typeName));
		
		if (DEBUG) System.out.println("Classifying " + bibRef.annotation.toXML());
		String typeName = "";
		
		//	got pagination ==> part of something
		boolean gotPagination = (bibRef.pagination != null);
		if (DEBUG) System.out.println(" - page data " + (gotPagination ? "" : "not ") + "given");
		
		//	got volume, issue, or number designator
		boolean gotPartDesignator = ((bibRef.volumeDesignator != null) || (bibRef.issueDesignator != null) || (bibRef.numberDesignator != null));
		if (DEBUG) System.out.println(" - part designator " + (gotPartDesignator ? "" : "not ") + "given");
		
		//	check book content hints
		boolean gotBookContentInfos = (bibRef.bookContentInfos.size() != 0);
		if (DEBUG) System.out.println(" - book content info " + (gotBookContentInfos ? "" : "not ") + "given");
		
		//	check for conference proceedings
		boolean gotConferenceProceedings = false;
		if (bibRef.journalOrPublisher != null) {
			for (int t = bibRef.journalOrPublisher.getStartIndex(); t < bibRef.journalOrPublisher.getEndIndex(); t++)
				if (this.conferenceSynonyms.containsIgnoreCase(bibRef.annotation.valueAt(t))) {
					gotConferenceProceedings = true;
					if (DEBUG) System.out.println(" - got proceedings volume title " + bibRef.journalOrPublisher.toXML());
					break;
				}
		}
		
		//	check for URL
		boolean gotUrl = (bibRef.urls.length > bibRef.dois.length);
		if (DEBUG && gotUrl) System.out.println(" - got URL " + bibRef.urls[0]);
		boolean gotNonFileUrl = (gotUrl && !bibRef.urls[0].getValue().toLowerCase().endsWith(".pdf"));
		if (DEBUG && gotNonFileUrl) System.out.println(" - got non-file URL " + bibRef.urls[0]);
		
		//	clearly a book
		if (gotBookContentInfos) {
			if (DEBUG) System.out.println(" --> using book content hint");
			typeName = (gotPagination ? BOOK_CHAPTER_REFERENCE_TYPE : BOOK_REFERENCE_TYPE);
		}
		
		//	clearly a journal or part of one
		else if (gotPartDesignator) {
			if (DEBUG) System.out.println(" --> using part designator hint");
			typeName = (gotPagination ? JOURNAL_ARTICEL_REFERENCE_TYPE : JOURNAL_VOLUME_REFERENCE_TYPE);
		}
		
		//	part of book or proceedings
		else if (gotPagination) {
			if (DEBUG) System.out.println(" --> using page data and journal / publisher name" + ((bibRef.journalOrPublisher == null) ? " (missing)" : (": " + TokenSequenceUtils.concatTokens(bibRef.journalOrPublisher, true, true))));
			typeName = (gotConferenceProceedings ? PROCEEDINGS_PAPER_REFERENCE_TYPE : BOOK_CHAPTER_REFERENCE_TYPE);
		}
		
		//	part of proceedings with missing page data
		else if (gotConferenceProceedings) {
			if (DEBUG) System.out.println(" --> using journal / publisher name: " + TokenSequenceUtils.concatTokens(bibRef.journalOrPublisher, true, true));
			typeName = PROCEEDINGS_PAPER_REFERENCE_TYPE;
		}
		
		//	web site (no part designators, pagination, or book content hint, non-DOI URL, and JoP absent or URL not pointing to fixed file)
		else if (gotNonFileUrl || (gotUrl && bibRef.journalOrPublisher == null)) {
			if (DEBUG) System.out.println(" --> using URL: " + bibRef.urls[0]);
			typeName = URL_REFERENCE_TYPE;
		}
		
		//	book or proceedings
		else {
			if (bibRef.title != null) {
				for (int t = bibRef.title.getStartIndex(); t < bibRef.title.getEndIndex(); t++)
					if (this.conferenceSynonyms.containsIgnoreCase(bibRef.annotation.valueAt(t))) {
						gotConferenceProceedings = true;
						if (DEBUG) System.out.println(" - got proceedings title " + bibRef.title.toXML());
						break;
					}
			}
			if (DEBUG) System.out.println(" --> using title" + ((bibRef.title == null) ? " (missing)" : (": " + TokenSequenceUtils.concatTokens(bibRef.title, true, true))));
			typeName = (gotConferenceProceedings ? PROCEEDINGS_REFERENCE_TYPE : BOOK_REFERENCE_TYPE); 
		}
		
		//	set type
		if (DEBUG) System.out.println(" ==> classified as " + typeName);
		bibRef.type = ((BibRefType) this.referenceTypes.get(typeName));
	}
	
	void learnDetails(MutableAnnotation bibRef) {
		
		//	learn author names, and also editor names, might be authors somewhere else
		Annotation[] feedbackAuthors = bibRef.getAnnotations(AUTHOR_ANNOTATION_TYPE);
		for (int a = 0; a < feedbackAuthors.length; a++)
			this.knownAuthors.addEntry(feedbackAuthors[a].getValue());
		Annotation[] feedbackEditors = bibRef.getAnnotations(EDITOR_ANNOTATION_TYPE);
		for (int e = 0; e < feedbackEditors.length; e++)
			this.knownAuthors.addEntry(feedbackEditors[e].getValue());
		
		//	TODO distinguish journal names from publishers and publisher locations
		boolean[] isJop = new boolean[bibRef.size()];
		Arrays.fill(isJop, false);
		Annotation[] feedbackJournalsAndPublishers = bibRef.getAnnotations(JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE);
		for (int jp = 0; jp < feedbackJournalsAndPublishers.length; jp++) {
			this.knownJournalsAndPublishers.addEntry(feedbackJournalsAndPublishers[jp].getValue());
			for (int t = feedbackJournalsAndPublishers[jp].getStartIndex(); t < feedbackJournalsAndPublishers[jp].getEndIndex(); t++)
				isJop[t] = true;
		}
		
		//	learn word functions
		for (int t = 0; t < bibRef.size(); t++) {
			String v = bibRef.valueAt(t);
			if (Gamta.isWord(v) && (v.length() > 1))
				this.jopWordStat.count(v, isJop[t], ((t == 0) || !isJop[t-1]), (((t+1) == bibRef.size()) || !isJop[t+1]));
		}
	}
	
	static class BibRefType implements Comparable {
		final String name;
		final String label;
		BibRefType(String name, String label) {
			this.name = name;
			this.label = label;
		}
		BibRefType(String name) {
			this.name = name;
			this.label = "COMPARISON DUMMY";
		}
		public int hashCode() {
			return this.name.hashCode();
		}
		public boolean equals(Object obj) {
			return ((obj instanceof BibRefType) && this.name.equals(((BibRefType) obj).name));
		}
		public int compareTo(Object obj) {
			return this.name.compareTo(((BibRefType) obj).name);
		}
		public String toString() {
			return this.label; // required for Swing version of feedback panel
		}
		public String toDataString() {
			return (this.name + "|" + this.label);
		}
		public static BibRefType parseDataString(String dataString) {
			String[] data = dataString.split("\\|");
			return ((data.length == 2) ? new BibRefType(data[0], data[1]) : null);
		}
	}
	
	//	use array of instances of this class as data containers instead of individual arrays ==> facilitates splitting 1,000 line parsing method
	private class BibRef {
		MutableAnnotation annotation;
		
		boolean[] nobleTitleToken;
		boolean[] nameListSeparator;
		boolean[] editorListLabel;
		
		Annotation[] authorNames;
		AuthorList[] authorLists;
		Annotation authorList;
		Annotation[] authors;
		
		Annotation[] editors;
		Annotation[] editorListLabels;
		
		Annotation[] years;
		Annotation year;
		
		Annotation[] urls;
		Annotation[] dois;
		Annotation[] labeledDates;
		Annotation urlAccessDate;
		
		Annotation[] pageNumbers;
		Annotation[] pageRanges;
		Annotation pagination;
		
		Annotation[] partDesignators;
		HashMap partDesignatorHints = new HashMap();
		Annotation[] volumeDesignators;
		Annotation volumeDesignator;
		Annotation[] issueDesignators;
		Annotation issueDesignator;
		Annotation[] numberDesignators;
		Annotation numberDesignator;
		Annotation[] seriesDesignators;
		Annotation seriesDesignator;
		Annotation[] fascicleDesignators;
		Annotation fascicleDesignator;
		
		Annotation[] numberDetailBlocks;
		Annotation numberDetailBlock;
		
		Annotation[] wordBlocks;
		boolean[] wordBlockExcluded;
		boolean[] boldToken;
		boolean[] italicsToken;
		
		Annotation journalOrPublisher;
		Annotation journal;
		Annotation publisher;
		Annotation location;
		Annotation proceedingsVolumeTitle;
		
		Annotation title;
		Annotation volumeTitle;
		
		BibRef parentRef;
		BibRef volumeRef;
		Annotation volumeReferencePrefix;
		Annotation volumeReference;
		
		ArrayList bookContentInfos = new ArrayList();
		boolean[] titleNumberToken;
		BibRefType type;
		
		boolean preExistingStructure = false;
		ArrayList structures = new ArrayList();
		Structure structure;
		
		BibRef(MutableAnnotation annot) {
			this.annotation = annot;
			
			int preExistingStructureScore = 0;
			if (this.annotation.getAnnotations(AUTHOR_ANNOTATION_TYPE).length != 0)
				preExistingStructureScore++;
			if (this.annotation.getAnnotations(TITLE_ANNOTATION_TYPE).length != 0)
				preExistingStructureScore++;
			if (this.annotation.getAnnotations(YEAR_ANNOTATION_TYPE).length != 0)
				preExistingStructureScore++;
			this.preExistingStructure = (preExistingStructureScore >= 2);
		}
	}
	
	private class Structure {
		Annotation bibRef;
		String[] details;
		
		String[] types;
		String typeString;
		String[] summary;
		String summaryString;
		String[] punctSummary;
		String punctSummaryString;
		
		String firstDetail;
		StringVector detailTypes = new StringVector();
		int detailTokenCount = 0;
		int maxVoidBlockLength = 0;
		
		Structure(Annotation bibRef, String[] workingStructure) {
			this.bibRef = bibRef;
			
			this.details = new String[workingStructure.length];
			System.arraycopy(workingStructure, 0, this.details, 0, workingStructure.length);
			
			int voidBlockLength = 0;
			for (int d = 0; d < this.details.length; d++) { 
				if (this.details[d] == null) {
					this.details[d] = "_";
					voidBlockLength++;
				}
				else {
					if (this.firstDetail == null)
						this.firstDetail = this.details[d];
					this.detailTypes.addElementIgnoreDuplicates(this.details[d]);
					this.detailTokenCount++;
					if (voidBlockLength > this.maxVoidBlockLength)
						this.maxVoidBlockLength = voidBlockLength;
					voidBlockLength = 0;
				}
			}
			if (voidBlockLength > this.maxVoidBlockLength)
				this.maxVoidBlockLength = voidBlockLength;
			
			this.types = this.detailTypes.toStringArray();
			this.typeString = this.detailTypes.concatStrings(" ");
			
			StringVector summary = new StringVector();
			String summaryLast = null;
			
			StringVector punctSummary = new StringVector();
			String punctSummaryLast = null;
			
			for (int d = 0; d < this.details.length; d++) {
				if ((d != 0) && YEAR_ANNOTATION_TYPE.equals(this.details[d-1]) && "_".equals(this.details[d]) && this.bibRef.valueAt(d).matches("[a-z]"))
					continue; // skip over single lower case letters following year of publication
				
				String summaryAdd = this.details[d];
				if ((d == 0) || !summaryLast.equals(summaryAdd)) {
					summary.addElement(summaryAdd);
					summaryLast = summaryAdd;
				}
				
				String punctSummaryAdd = (("_".equals(this.details[d]) && Gamta.isPunctuation(this.bibRef.valueAt(d))) ? this.bibRef.valueAt(d) : this.details[d]);
				if ((d == 0) || !punctSummaryLast.equals(punctSummaryAdd)) {
					punctSummary.addElement(punctSummaryAdd);
					punctSummaryLast = punctSummaryAdd;
				}
			}
			
			this.summary = summary.toStringArray();
			this.summaryString = summary.concatStrings(" ");
			
			for (int p = 0; p < punctSummary.size(); p++)
				if ("_".equals(punctSummary.get(p))) {
					for (int l = (p+1); l < punctSummary.size(); l++) {
						if (!Gamta.isPunctuation(punctSummary.get(l)))
							l = punctSummary.size();
						else if ("_".equals(punctSummary.get(l))) {
							while (p < l)
								punctSummary.removeElementAt(l--);
							l = punctSummary.size();
							p--;
						}
					}
				}
			
			this.punctSummary = punctSummary.toStringArray();
			this.punctSummaryString = punctSummary.concatStrings(" ");
		}
	}
	
//	private static final String namePartOrder = "npo";
//	private static final String firstLastNPO = "FL";
//	private static final String lastFirstNPO = "LF";
	
//	private static final String firstNameStyle = "fns";
//	private static final String fullNameFNS = "N";
//	private static final String initialsFNS = "I";
	
	private static final String etAlSpecialType = "etAl";
	private static final String authorListRepetitionMarkMarker = "alrm";
	private static final String knownAuthorMarker = "kam";
	private static final String authorNameListAttribute = "authorNameList";
	
	private static final String namePartOrderAttribute = "npo";
	private static final String firstNameStyleAttribute = "fns";
	private static final String initialsStyleAttribute = "ins";
	private static final String lastNameCaseAttribute = "lnc";
	
	private static final String caseAttribute = "case";
	private static final String allCaps = "AC";
	private static final String titleCase = "TC";
	
//	private static final String etAlSpecialType = "etAl";
//	private static final String repetitionMarkerSpecialType = "alrm";
//	private static final String knownAuthorMarker = "kam";
	private static final String institutionNameMarker = "inm";
	private static final String tailingStopWordsMarker = "tsw";
	
	private Annotation[] getAuthorNames(TokenSequence bibRef, boolean[] isTitleNumberToken, NameStyle nameStyle) {
		
		//	get last names
		Annotation[] authorLastNames = ProperNameUtils.getPersonLastNames(bibRef, nameStyle);
		
		//	add last names from lexicon ('Ng', etc.)
		Annotation[] knownAuthorLastNames = Gamta.extractAllContained(bibRef, this.knownAuthorLastNames, false);
		ArrayList knownAuthorLastNameList = new ArrayList();
		for (int n = 0; n < knownAuthorLastNames.length; n++) {
			String knownLastName = knownAuthorLastNames[n].getValue();
			if (knownLastName.equals(knownLastName.toLowerCase()))
				continue; // no use for all lower case
			if (knownLastName.equals(knownLastName.toUpperCase()))
				knownAuthorLastNames[n].setAttribute(caseAttribute, allCaps);
			else knownAuthorLastNames[n].setAttribute(caseAttribute, titleCase);
			knownAuthorLastNameList.add(knownAuthorLastNames[n]);
		}
		knownAuthorLastNames = ((Annotation[]) knownAuthorLastNameList.toArray(new Annotation[knownAuthorLastNameList.size()]));
		
		//	de-duplicate
		ArrayList authorLastNameList = new ArrayList();
		authorLastNameList.addAll(Arrays.asList(authorLastNames));
		authorLastNameList.addAll(Arrays.asList(knownAuthorLastNames));
		Collections.sort(authorLastNameList, AnnotationUtils.ANNOTATION_NESTING_ORDER);
		for (int n = 0; n < authorLastNameList.size(); n++) {
			Annotation lastName = ((Annotation) authorLastNameList.get(n));
			for (int cn = (n + 1); cn < authorLastNameList.size(); cn++) {
				Annotation cLastName = ((Annotation) authorLastNameList.get(cn));
				if (cLastName.getStartIndex() != lastName.getStartIndex())
					continue;
				if (cLastName.size() != lastName.size())
					continue;
				authorLastNameList.remove(cn--);
			}
		}
		authorLastNames = ((Annotation[]) authorLastNameList.toArray(new Annotation[authorLastNameList.size()]));
		
		//	collect all author names
		ArrayList authorNameList = new ArrayList();
		
		//	get full names
		Annotation[] authorNames = ProperNameUtils.getPersonNames(bibRef, authorLastNames, nameStyle);
		for (int n = 0; n < authorNames.length; n++) {
			if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("    - " + authorNames[n]);
			authorNames[n].changeTypeTo(AUTHOR_ANNOTATION_TYPE);
			authorNameList.add(authorNames[n]);
		}
		
		//	mark author names contained in dictionary, and sort out invalid ones and ones with invalid starts
		for (int a = 0; a < authorNameList.size(); a++) {
			Annotation authorName = ((Annotation) authorNameList.get(a));
			if (this.knownNonAuthorNameStarts.containsIgnoreCase(authorName.firstValue())) {
				authorNameList.remove(a--);
				continue;
			}
			String authorNameString = TokenSequenceUtils.concatTokens(authorName, true, true);
			if (this.knownNonAuthorNames.contains(authorNameString))
				authorNameList.remove(a--);
			else if (this.knownAuthorNames.containsIgnoreCase(authorNameString))
				authorName.setAttribute(knownAuthorMarker);
		}
		
		//	extract known author names (avoid duplication, though)
		HashSet authorNamePositions = new HashSet();
		for (int a = 0; a < authorNameList.size(); a++) {
			Annotation authorName = ((Annotation) authorNameList.get(a));
			authorNamePositions.add(authorName.getStartIndex() + "-" + authorName.getEndIndex());
		}		
		Annotation[] knownAuthorNames = Gamta.extractAllContained(bibRef, this.knownAuthorNames, false);
		if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("  - known author names");
		for (int kn = 0; kn < knownAuthorNames.length; kn++) {
			if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("    - " + knownAuthorNames[kn]);
			
			//	check for duplicates
			if (!authorNamePositions.add(knownAuthorNames[kn].getStartIndex() + "-" + knownAuthorNames[kn].getEndIndex())) {
				if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("     --> extracted by patterns");
				continue;
			}
			
			//	determine case
			String knownAuthorName = knownAuthorNames[kn].getValue();
			if (knownAuthorName.equals(knownAuthorName.toLowerCase()))
				continue; // no use for all lower case
			if (knownAuthorName.equals(knownAuthorName.toUpperCase()))
				knownAuthorNames[kn].setAttribute(caseAttribute, allCaps);
			else knownAuthorNames[kn].setAttribute(caseAttribute, titleCase);
			
			//	this one is actually new (wildcard style attributes)
			if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("     --> found author unmatched by patterns");
			knownAuthorNames[kn].setAttribute(namePartOrderAttribute, "*");
			knownAuthorNames[kn].setAttribute(firstNameStyleAttribute, "*");
			knownAuthorNames[kn].setAttribute(knownAuthorMarker);
			authorNameList.add(knownAuthorNames[kn]);
		}
		
		//	get institution names
		Annotation[] institutionAuthorNames = ProperNameUtils.getStraightProperNames(bibRef, nameStyle);
		if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("  - institutional author names");
		for (int n = 0; n < institutionAuthorNames.length; n++) {
			if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("    - " + institutionAuthorNames[n]);
			institutionAuthorNames[n].setAttribute(namePartOrderAttribute, "*");
			institutionAuthorNames[n].setAttribute(firstNameStyleAttribute, "*");
			institutionAuthorNames[n].setAttribute(institutionNameMarker);
			institutionAuthorNames[n].changeTypeTo(AUTHOR_ANNOTATION_TYPE);
			authorNameList.add(institutionAuthorNames[n]);
		}
		
		//	get institution name acronyms
		Annotation[] institutionAcronymAuthorNames = ProperNameUtils.getAcronyms(bibRef, nameStyle);
		if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("  - institutional acronym author names");
		for (int n = 0; n < institutionAcronymAuthorNames.length; n++) {
			if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("    - " + institutionAcronymAuthorNames[n]);
			institutionAcronymAuthorNames[n].setAttribute(namePartOrderAttribute, "*");
			institutionAcronymAuthorNames[n].setAttribute(firstNameStyleAttribute, "*");
			institutionAcronymAuthorNames[n].setAttribute(institutionNameMarker);
			institutionAcronymAuthorNames[n].changeTypeTo(AUTHOR_ANNOTATION_TYPE);
			authorNameList.add(institutionAcronymAuthorNames[n]);
		}
		
		//	add "et al." to author names (wildcard style attributes)
		Annotation[] etAlAuthorNames = Gamta.extractAllMatches(bibRef, "((et\\sal)|(\\&\\s*al)|(ET\\sAL)|(\\&\\s*AL))\\.?", false);
		for (int a = 0; a < etAlAuthorNames.length; a++) {
			etAlAuthorNames[a].changeTypeTo(etAlSpecialType);
			if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("    - " + etAlAuthorNames[a]);
			etAlAuthorNames[a].setAttribute(namePartOrderAttribute, "*");
			etAlAuthorNames[a].setAttribute(firstNameStyleAttribute, "*");
			authorNameList.add(etAlAuthorNames[a]);
			
			//	truncate dot from "et al." for <firstName> <lastName> part order ==> prevents "stealing" data element separator
			if (".".equals(etAlAuthorNames[a].lastValue())) {
				Annotation tEtAlAuthorName = Gamta.newAnnotation(bibRef, etAlAuthorNames[a].getType(), etAlAuthorNames[a].getStartIndex(), (etAlAuthorNames[a].size()-1));
				tEtAlAuthorName.setAttribute(namePartOrderAttribute, "*");
				tEtAlAuthorName.setAttribute(firstNameStyleAttribute, "*");
				authorNameList.add(tEtAlAuthorName);
			}
		}
		
		//	add author repetition markers
		Annotation[] repeatedAuthorNames = Gamta.extractAllMatches(bibRef, "([\\-]{3,}|[\\_]{3,})", false);
		for (int a = 0; a < repeatedAuthorNames.length; a++) {
			repeatedAuthorNames[a].changeTypeTo(AUTHOR_ANNOTATION_TYPE);
			if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("    - " + repeatedAuthorNames[a]);
			repeatedAuthorNames[a].setAttribute(namePartOrderAttribute, "*");
			repeatedAuthorNames[a].setAttribute(firstNameStyleAttribute, "*");
			repeatedAuthorNames[a].setAttribute(authorListRepetitionMarkMarker);
			authorNameList.add(repeatedAuthorNames[a]);
		}
		
		//	filter out editor list labels
		for (int a = 0; a < authorNameList.size(); a++) {
			Annotation authorName = ((Annotation) authorNameList.get(a));
			if (authorName.getValue().matches(this.editorListLabelRegEx))
				authorNameList.remove(a--);
		}
		
		//	filter out author list separators ('AND', etc.)
		for (int a = 0; a < authorNameList.size(); a++) {
			Annotation authorName = ((Annotation) authorNameList.get(a));
			if (this.authorListSeparators.containsIgnoreCase(authorName.getValue()))
				authorNameList.remove(a--);
		}
		
		//	filter out names whose ends are part of title numbers
		if (isTitleNumberToken != null) {
			if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("  - filtering for title numbers");
			for (int a = 0; a < authorNameList.size(); a++) {
				Annotation authorName = ((Annotation) authorNameList.get(a));
				if (authorName.getEndIndex() == bibRef.size())
					continue;
				boolean containsCommaPlusTitleNumber = false;
				boolean lastWasComma = false;
				for (int t = 0; t < authorName.size(); t++) {
					if (lastWasComma && isTitleNumberToken[authorName.getStartIndex() + t]) {
						containsCommaPlusTitleNumber = true;
						break;
					}
					lastWasComma = ",".equals(authorName.valueAt(t));
				}
				if (containsCommaPlusTitleNumber) {
					if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("     --> removed author overlapping with title number: " + authorName);
					authorNameList.remove(a--);
				}
			}
		}
		
		//	finally ...
		authorNames = ((Annotation[]) authorNameList.toArray(new Annotation[authorNameList.size()]));
		Arrays.sort(authorNames, AnnotationUtils.ANNOTATION_NESTING_ORDER);
		return authorNames;
	}
	
	private static class AuthorList {
		Annotation editorListLabel;
		char editorListLabelPos = '*';
		boolean isSubList = false;
		boolean isInstitutionName = false;
		boolean hasRepetitionMarker = false;
		Annotation annotation;
		ArrayList authorNames = new ArrayList();
		LinkedHashSet namePartOrders = new LinkedHashSet();
		LinkedHashSet firstNameStyles = new LinkedHashSet();
		LinkedHashSet initialsStyles = new LinkedHashSet();
		LinkedHashSet lastNameCases = new LinkedHashSet();
		boolean tailingStopWords = false;
		CountingSet bridged = new CountingSet();
		AuthorList(Annotation bibRef, Annotation authorList, ArrayList authorNames, boolean[] isNobleTitleToken) {
			
			//	assess author name style as well as bridged tokens
			int startIndex = -1;
			int endIndex = -1;
			for (int a = 0; a < authorNames.size(); a++) {
				Annotation authorName = ((Annotation) authorNames.get(a));
				this.authorNames.add(authorName);
				if (authorName.hasAttribute(institutionNameMarker))
					this.isInstitutionName = true;
				else if (authorName.hasAttribute(authorListRepetitionMarkMarker))
					this.hasRepetitionMarker = true;
				else {
					this.namePartOrders.add(authorName.getAttribute(namePartOrderAttribute));
					this.firstNameStyles.add(authorName.getAttribute(firstNameStyleAttribute));
					if (authorName.hasAttribute(initialsStyleAttribute))
						this.initialsStyles.add(authorName.getAttribute(initialsStyleAttribute));
					this.firstNameStyles.add(authorName.getAttribute(firstNameStyleAttribute));
					this.lastNameCases.add(authorName.getAttribute(lastNameCaseAttribute));
					this.tailingStopWords = authorName.hasAttribute(tailingStopWordsMarker);
				}
				if (startIndex == -1)
					startIndex = authorName.getStartIndex();
				else for (int b = endIndex; b < authorName.getStartIndex(); b++) {
					if (!isNobleTitleToken[b])
						this.bridged.add(bibRef.valueAt(b));
				}
				endIndex = authorName.getEndIndex();
			}
			
			this.annotation = authorList;
			
			if (this.annotation.hasAttribute("leadEditorListLabel")) {
				this.editorListLabel = ((Annotation) this.annotation.getAttribute("leadEditorListLabel"));
				this.editorListLabelPos = 'L';
			}
			else if (this.annotation.hasAttribute("tailEditorListLabel")) {
				this.editorListLabel = ((Annotation) this.annotation.getAttribute("tailEditorListLabel"));
				this.editorListLabelPos = 'T';
			}
		}
		
		static final Comparator authorListOrder = new Comparator() {
			public int compare(Object obj1, Object obj2) {
				AuthorList al1 = ((AuthorList) obj1);
				AuthorList al2 = ((AuthorList) obj2);
				int c = AnnotationUtils.compare(al1.annotation, al2.annotation);
				if (c != 0)
					return c; // prefer early-starting long author lists
				c = (al2.authorNames.size() - al1.authorNames.size());
				if (c != 0)
					return c; // prefer author lists with more names
				c = (al1.bridged.size() - al2.bridged.size());
				if (c != 0)
					return c; // prefer more compact author lists
				c = (al1.namePartOrders.size() - al2.namePartOrders.size());
				if (c != 0)
					return c; // prefer more style consistent author lists
				c = (al1.firstNameStyles.size() - al2.firstNameStyles.size());
				if (c != 0)
					return c; // prefer more style consistent author lists
				c = (al1.initialsStyles.size() - al2.initialsStyles.size());
				if (c != 0)
					return c; // prefer more style consistent author lists
				return 0; // nothing to tell these two apart
			}
		};
	}
	
	private boolean[] markNobleTitleTokens(BibRef bibRef, Annotation bibRefAnnot) {
		if ((bibRef != null) && (bibRef.nobleTitleToken != null) && (bibRef.nobleTitleToken.length == bibRefAnnot.size()))
			return bibRef.nobleTitleToken;
		
		//	mark tokens belonging to noble titles
		Annotation[] nobleTitles = Gamta.extractAllMatches(bibRefAnnot, this.nobleTitleNameRegEx, false);
		boolean[] isNobleTitleToken = createTokenFilter(bibRefAnnot, null);
		if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  - possible noble titles:");
		for (int n = 0; n < nobleTitles.length; n++) {
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("    - " + nobleTitles[n]);
			if (this.nobleTitleStarts.contains(nobleTitles[n].firstValue())) {
				augmentFilteredTokens(isNobleTitleToken, nobleTitles[n], null);
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("    --> marked");
			}
			else if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("    --> ignored for strange start");
		}
		
		//	store overlay for later use in author list gap recovery
		if (bibRef != null)
			bibRef.nobleTitleToken = isNobleTitleToken;
		
		//	finally ...
		return isNobleTitleToken;
	}
	
	private boolean[] markNameListSeparators(BibRef bibRef, Annotation bibRefAnnot, Annotation[] authorListSeparators, Annotation[] authorListEndSeparators) {
		if ((bibRef != null) && (bibRef.nameListSeparator != null) && (bibRef.nameListSeparator.length == bibRefAnnot.size()))
			return bibRef.nameListSeparator;
		
		//	mark name list separators
		boolean[] isNameListSeparator = createTokenFilter(bibRefAnnot, null);
		augmentFilteredTokens(isNameListSeparator, authorListSeparators, null);
		augmentFilteredTokens(isNameListSeparator, authorListEndSeparators, null);
		
		//	store overlay for later use in author list gap recovery
		if (bibRef != null)
			bibRef.nameListSeparator = isNameListSeparator;
		
		//	finally ...
		return isNameListSeparator;
	}
	
	//	TODO TEST revistaPeruanaBiologia.22.3.289-296.pdf.xml (name part order flip)
	//	TODO TEST jPalaeogeography.s42501-018-0014-2.pdf.xml (name part order flip)
	private AuthorList[] getAuthorLists(BibRef bibRef, Annotation bibRefAnnot, Annotation[] authorNames, DocumentStyle authorNameStyle) {
		
		//	make sure to have noble title tokens marked
		boolean[] isNobleTitleToken = this.markNobleTitleTokens(bibRef, bibRefAnnot);
		
		//	get name part order (if any)
		String namePartOrder = authorNameStyle.getStringProperty("namePartOrder", null);
		
		//	sort author names in startAuthorName, continueAuthorName, and endAuthorName categories
		ArrayList singleAuthorNames = new ArrayList();
		ArrayList startAuthorNames = new ArrayList();
		ArrayList continueAuthorNames = new ArrayList();
		ArrayList endAuthorNames = new ArrayList();
		ArrayList etAlAuthorNames = new ArrayList();
		if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Starting with " + authorNames.length + " author names");
		for (int a = 0; a < authorNames.length; a++) {
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println(" - " + authorNames[a].toXML());
			
			//	'et al.' is always at the very end, and never up front
			if (etAlSpecialType.equals(authorNames[a].getType())) {
				endAuthorNames.add(authorNames[a]);
				etAlAuthorNames.add(authorNames[a]);
				continue;
			}
			
			//	author list repetition markers are always at the very beginning
			if (authorNames[a].hasAttribute(authorListRepetitionMarkMarker)) {
				startAuthorNames.add(authorNames[a]);
				continue;
			}
			
			//	institutional author names never combine with any other author names
			if (authorNames[a].hasAttribute(institutionNameMarker)) {
				singleAuthorNames.add(authorNames[a]);
				continue;
			}
			
			//	get matched name part order
			String anNpo = ((String) authorNames[a].getAttribute(namePartOrderAttribute, "*"));
			
			//	wildcard fits everywhere, as does any name under an unknown name part order
			if ("*".equals(anNpo) || (namePartOrder == null)) {
				startAuthorNames.add(authorNames[a]);
				continueAuthorNames.add(authorNames[a]);
				endAuthorNames.add(authorNames[a]);
			}
			
			//	starting name only
			else if (namePartOrder.startsWith(anNpo + "+"))
				startAuthorNames.add(authorNames[a]);
			
			//	continuing or ending name only
			else if (namePartOrder.endsWith("+" + anNpo)) {
				continueAuthorNames.add(authorNames[a]);
				endAuthorNames.add(authorNames[a]);
			}
			
			//	we have a single name part order, so names fit everywhere
			else {
				startAuthorNames.add(authorNames[a]);
				continueAuthorNames.add(authorNames[a]);
				endAuthorNames.add(authorNames[a]);
			}
		}
		if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Got " + startAuthorNames.size() + " starting author names, " + continueAuthorNames.size() + " continuing ones, " + endAuthorNames.size() + " ending ones, and " + singleAuthorNames.size() + " single ones");
		
		//	get list separator(s) as a single pattern
		String authorListSeparatorPattern = authorNameStyle.getStringProperty("nameListSeparatorPattern", "(\\,|\\;|\\&|and|et|e|y|und)");
		Annotation[] authorListSeparators = Gamta.extractAllMatches(bibRefAnnot, authorListSeparatorPattern, true);
		String authorListEndSeparatorPattern = authorNameStyle.getStringProperty("nameListEndSeparatorPattern", "((\\,\\;\\s*\\&)|(\\,\\s*and)|\\,|\\;|\\&|and|et|e|y|und)");
		Annotation[] authorListEndSeparators = Gamta.extractAllMatches(bibRefAnnot, authorListEndSeparatorPattern, true);
		
		//	filter start author names if too many (see above) to prevent combinatoric runaway
		if (startAuthorNames.size() > 25) {
			filterStartAuthorNames(startAuthorNames, authorListSeparators);
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Got " + startAuthorNames.size() + " starting author names after filtering");
		}
		
		//	index categorized author names
		AnnotationIndex authorListPartIndex = new AnnotationIndex();
		
		//	index starting author names as (expandable) seed author lists
		for (int a = 0; a < startAuthorNames.size(); a++)
			((Annotation) startAuthorNames.get(a)).setAttribute("expandable", "true");
		authorListPartIndex.addAnnotations(((Annotation[]) startAuthorNames.toArray(new Annotation[startAuthorNames.size()])), "authorList");
		
		//	index other author names
		authorListPartIndex.addAnnotations(((Annotation[]) continueAuthorNames.toArray(new Annotation[continueAuthorNames.size()])), "cAuthorName");
		authorListPartIndex.addAnnotations(((Annotation[]) endAuthorNames.toArray(new Annotation[endAuthorNames.size()])), "eAuthorName");
		authorListPartIndex.addAnnotations(((Annotation[]) etAlAuthorNames.toArray(new Annotation[etAlAuthorNames.size()])), "etAlAuthorName");
		
		//	index separators
		authorListPartIndex.addAnnotations(authorListSeparators, "separator");
		if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Separators are " + Arrays.toString(authorListSeparators));
		authorListPartIndex.addAnnotations(authorListEndSeparators, "endSeparator");
		if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("End separators are " + Arrays.toString(authorListEndSeparators));
		
		//	assemble author lists
		ArrayList authorListAnnots = new ArrayList();
		HashSet authorListStrings = new HashSet();
		
		//	mark institutional author names as author lists
		for (int a = 0; a < singleAuthorNames.size(); a++) {
			Annotation authorName = ((Annotation) singleAuthorNames.get(a));
			Annotation authorList = Gamta.newAnnotation(bibRefAnnot, AUTHOR_LIST_ANNOTATION_TYPE, authorName.getStartIndex(), authorName.size());
			authorListAnnots.add(authorList);
			authorListStrings.add(authorList.getValue());
			ArrayList authorNameList = new ArrayList();
			authorNameList.add(authorName);
			authorList.setAttribute(authorNameListAttribute, authorNameList);
			if (authorName.hasAttribute(institutionNameMarker))
				authorList.setAttribute(institutionNameMarker);
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Added author list " + authorList.toXML());
		}
		
		//	mark individual seed author names as author lists
		for (int a = 0; a < startAuthorNames.size(); a++) {
			Annotation authorName = ((Annotation) startAuthorNames.get(a));
			Annotation authorList = Gamta.newAnnotation(bibRefAnnot, AUTHOR_LIST_ANNOTATION_TYPE, authorName.getStartIndex(), authorName.size());
			authorListAnnots.add(authorList);
			authorListStrings.add(authorList.getValue());
			ArrayList authorNameList = new ArrayList();
			authorNameList.add(authorName);
			authorList.setAttribute(authorNameListAttribute, authorNameList);
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Added author list " + authorList.toXML());
		}
		
		//	expand seed author lists
		ArrayList newAuthorListAnnots = new ArrayList();
		HashSet newAuthorListStrings = new HashSet();
		do {
			System.out.println("Attempting expansion");
			newAuthorListAnnots.clear();
			newAuthorListStrings.clear();
			MatchTree[] authorListMatches = AnnotationPatternMatcher.getMatchTrees(bibRefAnnot, authorListPartIndex, "<authorList expandable=\"true\"> <separator> <cAuthorName>");
			System.out.println(" - got " + authorListMatches.length + " expanded matches");
			for (int l = 0; l < authorListMatches.length; l++) {
				Annotation authorList = authorListMatches[l].getMatch();
				authorList.changeTypeTo(AUTHOR_LIST_ANNOTATION_TYPE);
				finishAuthorNameList(authorListMatches[l], authorList);
				newAuthorListAnnots.add(authorList);
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Added author list " + authorList.toXML());
				if (authorListStrings.add(authorList.getValue()))
					newAuthorListStrings.add(authorList.getValue());
			}
			authorListAnnots.addAll(newAuthorListAnnots);
			authorListPartIndex.addAnnotations(((Annotation[]) newAuthorListAnnots.toArray(new Annotation[newAuthorListAnnots.size()])), "authorList");
		} while (newAuthorListStrings.size() != 0);
		
		//	finalize author lists
//		MatchTree[] authorListMatches = AnnotationPatternMatcher.getMatchTrees(bibRefAnnot, authorListPartIndex, "<authorList expandable=\"true\"> ((<separator>|<endSeparator>) (<cAuthorName>|<eAuthorName>))?");
		MatchTree[] authorListMatches = AnnotationPatternMatcher.getMatchTrees(bibRefAnnot, authorListPartIndex, "<authorList> ((<separator>|<endSeparator>) (<cAuthorName>|<eAuthorName>))?");
		for (int l = 0; l < authorListMatches.length; l++) {
			Annotation authorList = authorListMatches[l].getMatch();
			authorList.changeTypeTo(AUTHOR_LIST_ANNOTATION_TYPE);
			finishAuthorNameList(authorListMatches[l], authorList);
			authorListAnnots.add(authorList);
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Added terminated author list " + authorList.toXML());
		}
		authorListAnnots.addAll(newAuthorListAnnots);
		
		//	finalize author lists
		authorListMatches = AnnotationPatternMatcher.getMatchTrees(bibRefAnnot, authorListPartIndex, "<authorList> <etAlAuthorName>");
		for (int l = 0; l < authorListMatches.length; l++) {
			Annotation authorList = authorListMatches[l].getMatch();
			authorList.changeTypeTo(AUTHOR_LIST_ANNOTATION_TYPE);
			finishAuthorNameList(authorListMatches[l], authorList);
			authorListAnnots.add(authorList);
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Added 'et al.' terminated author list " + authorList.toXML());
		}
		
		//	get editor list labels
		Annotation[] editorListLabels = Gamta.extractAllMatches(bibRefAnnot, this.editorListLabelRegEx);
		if (editorListLabels.length != 0) {
			
			//	index editor list labels (leading ones only without parentheses)
			for (int l = 0; l < editorListLabels.length; l++) {
				if (Gamta.isWord(editorListLabels[l].firstValue()))
					authorListPartIndex.addAnnotations(editorListLabels, "lEditorListLabel");
				authorListPartIndex.addAnnotation(editorListLabels[l], "tEditorListLabel");
			}
			
			//	attach leading editor list labels
			authorListMatches = AnnotationPatternMatcher.getMatchTrees(bibRefAnnot, authorListPartIndex, "<lEditorListLabel> ':'? <authorList>");
			for (int l = 0; l < authorListMatches.length; l++) {
				Annotation authorList = authorListMatches[l].getMatch();
				authorList.changeTypeTo(AUTHOR_LIST_ANNOTATION_TYPE);
				finishAuthorNameList(authorListMatches[l], authorList);
				authorListAnnots.add(authorList);
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Added editor list labeled author list " + authorList.toXML());
			}
			
			//	attach tailing editor list labels
			authorListMatches = AnnotationPatternMatcher.getMatchTrees(bibRefAnnot, authorListPartIndex, "<authorList> ','? <tEditorListLabel>");
			for (int l = 0; l < authorListMatches.length; l++) {
				Annotation authorList = authorListMatches[l].getMatch();
				authorList.changeTypeTo(AUTHOR_LIST_ANNOTATION_TYPE);
				finishAuthorNameList(authorListMatches[l], authorList);
				authorListAnnots.add(authorList);
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Added editor list label terminated author list " + authorList.toXML());
			}
		}
		
		//	sort all author lists found
		Collections.sort(authorListAnnots, AnnotationUtils.ANNOTATION_NESTING_ORDER);
		
		//	TODO maybe even do this across all paragraphs for better accuracy
		
		//	eliminate duplicate author lists
		for (int l = 0; l < authorListAnnots.size(); l++) {
			Annotation authorList = ((Annotation) authorListAnnots.get(l));
			for (int cl = (l+1); cl < authorListAnnots.size(); cl++) {
				Annotation cAuthorList = ((Annotation) authorListAnnots.get(cl));
				if (AnnotationUtils.equals(cAuthorList, authorList) && (authorList.hasAttribute(institutionNameMarker) == cAuthorList.hasAttribute(institutionNameMarker)))
					authorListAnnots.remove(cl--);
				else if (authorList.getEndIndex() <= cAuthorList.getStartIndex())
					break;
			}
		}
		
		//	remove author lists nested in labeled editor lists
		for (int l = 0; l < authorListAnnots.size(); l++) {
			Annotation authorList = ((Annotation) authorListAnnots.get(l));
			if (!authorList.hasAttribute("leadEditorListLabel") && !authorList.hasAttribute("tailEditorListLabel"))
				continue;
			for (int cl = (l+1); cl < authorListAnnots.size(); cl++) {
				Annotation cAuthorList = ((Annotation) authorListAnnots.get(cl));
				if (AnnotationUtils.liesIn(cAuthorList, authorList))
					authorListAnnots.remove(cl--);
				else if (authorList.getEndIndex() <= cAuthorList.getStartIndex())
					break;
			}
		}
		
		//	wrap final author lists
		ArrayList authorLists = new ArrayList();
		for (int l = 0; l < authorListAnnots.size(); l++) {
			Annotation authorList = ((Annotation) authorListAnnots.get(l));
			ArrayList authorNameList = ((ArrayList) authorList.getAttribute(authorNameListAttribute));
			AuthorList al = new AuthorList(bibRefAnnot, authorList, authorNameList, isNobleTitleToken);
			authorLists.add(al);
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) {
				System.out.println("Got author list " + authorList.toXML());
				System.out.println(" - " + AuthorListStyle.getKey(al));
			}
		}
		
		/* eliminate author lists with tailing stop words or tailing un-dotted initial immediately folowed by
		 * (a) a lower case word that is not a name separator, or
		 * (b) any word if the last word is 'in' (most likely volume reference label) */
		boolean[] isNameListSeparator = this.markNameListSeparators(bibRef, bibRefAnnot, authorListSeparators, authorListEndSeparators);
		for (int l = 0; l < authorLists.size(); l++) {
			AuthorList authorList = ((AuthorList) authorLists.get(l));
			if (authorList.annotation.getEndIndex() == bibRefAnnot.size())
				continue; // no following word at all
			if (!authorList.tailingStopWords && !authorList.annotation.lastValue().matches("[A-Z][a-z]?"))
				continue; // no tailing stop words or un-dotted initial that could be an overrun
			String followingToken = bibRefAnnot.valueAt(authorList.annotation.getEndIndex());
			if (!Gamta.isWord(followingToken))
				continue; // this one should be safe
			if (isNameListSeparator[authorList.annotation.getEndIndex()])
				continue; // author list separators are allowed
			if (!followingToken.equals(followingToken.toLowerCase()) && !"in".equalsIgnoreCase(authorList.annotation.lastValue()))
				continue; // not a lower case word, and no tailing 'in'
			authorLists.remove(l--);
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Eliminated author list followed by lower case token '" + followingToken + "' " + authorList.annotation.toXML());
		}
		
		//	eliminate author lists nested in others with same style
		for (int l = 0; l < authorLists.size(); l++) {
			AuthorList authorList = ((AuthorList) authorLists.get(l));
			for (int cl = (l+1); cl < authorLists.size(); cl++) {
				AuthorList cAuthorList = ((AuthorList) authorLists.get(cl));
				if (AnnotationUtils.liesIn(cAuthorList.annotation, authorList.annotation) && authorList.namePartOrders.equals(cAuthorList.namePartOrders) && authorList.firstNameStyles.equals(cAuthorList.firstNameStyles) && (!authorList.tailingStopWords || cAuthorList.tailingStopWords)) {
					authorLists.remove(cl--);
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Eliminated nested author list " + cAuthorList.annotation.toXML());
				}
				else if (authorList.annotation.getEndIndex() <= cAuthorList.annotation.getStartIndex())
					break;
			}
		}
//		
//		//	flag author lists labeled as editor lists
//		if (editorListLabels.length != 0) {
//			boolean[] isEditorListLabel = createTokenFilter(bibRef.annotation, editorListLabels);
//			for (int l = 0; l < authorLists.size(); l++) {
//				AuthorList authorList = ((AuthorList) authorLists.get(l));
//				if ((authorList.annotation.getEndIndex() < bibRef.annotation.size()) && isEditorListLabel[authorList.annotation.getEndIndex()])
//					authorList.hasEditorListLabel = true;
//			}
//		}
		
		//	finally ...
		return ((AuthorList[]) authorLists.toArray(new AuthorList[authorLists.size()]));
	}
	
	private static void filterStartAuthorNames(ArrayList startAuthorNames, Annotation[] authorListSeparators) {
		if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Filtering " + startAuthorNames.size() + " starting author names:");
		
		//	index start author names by name part order, and get overall range
		HashMap sansByNpo = new HashMap();
		int minSanStartIndex = Integer.MAX_VALUE;
		int maxSanEndIndex = 0;
		for (int n = 0; n < startAuthorNames.size(); n++) {
			Annotation san = ((Annotation) startAuthorNames.get(n));
			
			//	index by a,e part order
			String sanNpo = ("" + san.getAttribute(namePartOrderAttribute));
			ArrayList sans = ((ArrayList) sansByNpo.get(sanNpo));
			if (sans == null) {
				sans = new ArrayList();
				sansByNpo.put(sanNpo, sans);
			}
			sans.add(san);
			
			//	update range
			minSanStartIndex = Math.min(minSanStartIndex, san.getStartIndex());
			maxSanEndIndex = Math.max(maxSanEndIndex, san.getEndIndex());
		}
		startAuthorNames.clear();
		
		//	build separator overlay
		boolean[] isSeparator = new boolean[maxSanEndIndex];
		Arrays.fill(isSeparator, false);
		for (int s = 0; s < authorListSeparators.length; s++) {
			if (maxSanEndIndex <= authorListSeparators[s].getEndIndex())
				break;
			for (int t = authorListSeparators[s].getStartIndex(); t < authorListSeparators[s].getEndIndex(); t++)
				isSeparator[t] = true;
		}
		
		//	re-populate start author names
		for (Iterator npoit = sansByNpo.keySet().iterator(); npoit.hasNext();) {
			String npo = ((String) npoit.next());
			ArrayList sans = ((ArrayList) sansByNpo.get(npo));
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println(" - filtering " + sans.size() + " " + npo + " author names");
			
			//	too few names to justify filtering hassle
			if (sans.size() < 2) {
				startAuthorNames.addAll(sans);
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("     ==> retained all (count)");
				continue;
			}
			
			//	too short a range to justify filtering hassle
			if ((maxSanEndIndex - minSanStartIndex) < 25) {
				startAuthorNames.addAll(sans);
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("     ==> retained all (range)");
				continue;
			}
			
			//	create overlay (wasting a few leading booleans, if any, should be cheaper than working with index shift)
			boolean[] isSan = new boolean[maxSanEndIndex];
			Arrays.fill(isSan, false);
			for (int n = 0; n < sans.size(); n++) {
				Annotation san = ((Annotation) sans.get(n));
				for (int t = san.getStartIndex(); t < san.getEndIndex(); t++)
					isSan[t] = true;
			}
			int[] lastGapDist = new int[maxSanEndIndex];
			lastGapDist[minSanStartIndex] = 0;
			lastGapDist[minSanStartIndex + 1] = 1;
			for (int t = (minSanStartIndex + 2); t < lastGapDist.length; t++) {
				if (isSan[t-1] || isSan[t-2])
					lastGapDist[t] = (lastGapDist[t-1] + 1);
				else lastGapDist[t] = 0;
			}
			
			//	filter author names
			for (int n = 0; n < sans.size(); n++) {
				Annotation san = ((Annotation) sans.get(n));
				if ((san.getStartIndex() == 0) || !isSeparator[san.getStartIndex()-1]) {
					startAuthorNames.add(san);
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("     --> retained (no separator) " + san.toXML());
				}
				else if (lastGapDist[san.getStartIndex()] < 10) {
					startAuthorNames.add(san);
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("     --> retained (gap) " + san.toXML());
				}
				else if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("     --> removed " + san.toXML());
			}
		}
		
		//	make sure to re-establish sort order
		Collections.sort(startAuthorNames, AnnotationUtils.ANNOTATION_NESTING_ORDER);
	}
	
	private static void finishAuthorNameList(MatchTree authorListMatch, Annotation authorList) {
		finishAuthorNameList(authorListMatch.getChildren(), authorList);
		authorList.setAttribute("expandable", "true"); // we should try and expand this one further
	}
	
	private static void finishAuthorNameList(MatchTreeNode[] mtns, Annotation authorList) {
		for (int n = 0; n < mtns.length; n++) {
			if (mtns[n].getPattern().startsWith("<")) {
				if (mtns[n].getPattern().startsWith("<authorList")) {
					if (AUTHOR_ANNOTATION_TYPE.equals(mtns[n].getMatch().getType())) {
						ArrayList authorNameList = new ArrayList();
						authorNameList.add(mtns[n].getMatch());
						authorList.setAttribute(authorNameListAttribute, authorNameList);
					}
					else if (AUTHOR_LIST_ANNOTATION_TYPE.equals(mtns[n].getMatch().getType())) {
						ArrayList authorNameList = ((ArrayList) mtns[n].getMatch().getAttribute(authorNameListAttribute));
						if (authorNameList != null) {
							authorNameList = new ArrayList(authorNameList); // copy for later expansion
							authorList.setAttribute(authorNameListAttribute, authorNameList);
						}
					}
					mtns[n].getMatch().removeAttribute("expandable"); // no use expanding this one any further
				}
				else if (mtns[n].getPattern().startsWith("<cAuthorName") || mtns[n].getPattern().startsWith("<eAuthorName")) {
					ArrayList authorNameList = ((ArrayList) authorList.getAttribute(authorNameListAttribute));
					if (authorNameList != null)
						authorNameList.add(mtns[n].getMatch());
				}
				else if (mtns[n].getPattern().startsWith("<lEditorListLabel"))
					authorList.setAttribute("leadEditorListLabel", mtns[n].getMatch());
				else if (mtns[n].getPattern().startsWith("<tEditorListLabel"))
					authorList.setAttribute("tailEditorListLabel", mtns[n].getMatch());
			}
			else {
				MatchTreeNode[] cMtns = mtns[n].getChildren();
				if (cMtns != null)
					finishAuthorNameList(cMtns, authorList);
			}
		}
	}
	
	static class AuthorListStyle implements Comparable {
		final String key;
		LinkedHashSet namePartOrders = new LinkedHashSet();
		HashSet firstNameStyles = new HashSet();
		HashSet initialsStyles = new HashSet();
		HashSet lastNameCases = new HashSet();
		HashSet refIDs = new HashSet();
		//ArrayList instances = new ArrayList();
		int instanceCount = 0;
		int nameCount = 0;
		int tokenCount = 0;
		CountingSet bridged = new CountingSet(new TreeMap());
		CountingSet startDistances = new CountingSet(new TreeMap());
		CountingSet endDistances = new CountingSet(new TreeMap());
		float alignmentScore = 0;
		boolean isLeading = true;
		AuthorListStyle(AuthorList al) {
			this.key = getKey(al);
			this.namePartOrders.addAll(al.namePartOrders);
			this.firstNameStyles.addAll(al.firstNameStyles);
			this.initialsStyles.addAll(al.initialsStyles);
			this.lastNameCases.addAll(al.lastNameCases);
		}
		boolean isCompatible(AuthorList al) {
			return (
					(this.namePartOrders.contains("*") || this.namePartOrders.containsAll(al.namePartOrders))
					&&
					(this.firstNameStyles.contains("*") || this.firstNameStyles.containsAll(al.firstNameStyles))
					&&
					(this.lastNameCases.contains("*") || this.lastNameCases.containsAll(al.lastNameCases))
				);
		}
		boolean isCompatible(Annotation authorName) {
			return ((this.namePartOrders.contains("*") || this.namePartOrders.contains(authorName.getAttribute(namePartOrderAttribute))) && (this.firstNameStyles.contains("*") || this.firstNameStyles.contains(authorName.getAttribute(firstNameStyleAttribute))) && (this.lastNameCases.contains("*") || this.lastNameCases.contains(authorName.getAttribute(lastNameCaseAttribute))));
		}
		public int compareTo(Object obj) {
			return this.key.compareTo(((AuthorListStyle) obj).key);
		}
		static String getKey(AuthorList al) {
			return (al.namePartOrders + "-" + al.firstNameStyles + "-" + al.lastNameCases);
		}
	}
	
	private AuthorListStyle getAuthorListStyle(BibRef[] bibRefs) {
		
		//	cluster author lists by size and style
		LinkedHashMap authorListStyles = new LinkedHashMap();
		for (int r = 0; r < bibRefs.length; r++) {
			if (bibRefs[r].preExistingStructure)
				continue;
			
			//	mark nested sub lists
			Arrays.sort(bibRefs[r].authorLists, AuthorList.authorListOrder);
			for (int l = 0; l < bibRefs[r].authorLists.length; l++) {
				for (int ll = (l+1); ll < bibRefs[r].authorLists.length; ll++) {
					if (bibRefs[r].authorLists[l].annotation.getEndIndex() <= bibRefs[r].authorLists[ll].annotation.getStartIndex())
						break; // no further nesting relations to come
					if (bibRefs[r].authorLists[l].annotation.getEndIndex() < bibRefs[r].authorLists[ll].annotation.getEndIndex())
						continue; // not nested
					if (!bibRefs[r].authorLists[l].namePartOrders.containsAll(bibRefs[r].authorLists[ll].namePartOrders))
						continue; // not a sub list
					if (!bibRefs[r].authorLists[l].firstNameStyles.containsAll(bibRefs[r].authorLists[ll].firstNameStyles))
						continue; // not a sub list
					if (!bibRefs[r].authorLists[l].lastNameCases.containsAll(bibRefs[r].authorLists[ll].lastNameCases))
						continue; // not a sub list
					if (bibRefs[r].authorLists[l].annotation.size() <= bibRefs[r].authorLists[ll].annotation.size())
						continue; // not a sub list
					bibRefs[r].authorLists[ll].isSubList = true;
				}
			}
			
			//	cluster the author lists
			for (int l = 0; l < bibRefs[r].authorLists.length; l++) {
				if (bibRefs[r].authorLists[l].isInstitutionName)
					continue; // let's not generate empty styles
				if (bibRefs[r].authorLists[l].hasRepetitionMarker && (bibRefs[r].authorLists[l].authorNames.size() == 1))
					continue; // let's still not generate empty styles
				countAuthorListToStyle(bibRefs[r].authorLists[l], bibRefs[r], bibRefs.length, authorListStyles);
				
				//	support only if no LF-FL candidate available for this reference!!
				if (bibRefs[r].authorLists[l].isSubList)
					continue;
				
				//	more than one author name, if there is a name part order flip, we already got it
				if (bibRefs[r].authorLists[l].authorNames.size() > 1)
					continue;
				
				//	single name list in last-first order, have to support order switching style
				if (bibRefs[r].authorLists[l].namePartOrders.contains("LnFn")) {
					bibRefs[r].authorLists[l].namePartOrders.add("FnLn");
					countAuthorListToStyle(bibRefs[r].authorLists[l], bibRefs[r], bibRefs.length, authorListStyles);
					bibRefs[r].authorLists[l].namePartOrders.remove("FnLn");
					
					if (bibRefs[r].authorLists[l].firstNameStyles.contains("I")) {
						bibRefs[r].authorLists[l].namePartOrders.add("InLn");
						countAuthorListToStyle(bibRefs[r].authorLists[l], bibRefs[r], bibRefs.length, authorListStyles);
						bibRefs[r].authorLists[l].namePartOrders.remove("InLn");
					}
				}
				else if (bibRefs[r].authorLists[l].namePartOrders.contains("LnIn")) {
					bibRefs[r].authorLists[l].namePartOrders.add("InLn");
					countAuthorListToStyle(bibRefs[r].authorLists[l], bibRefs[r], bibRefs.length, authorListStyles);
					bibRefs[r].authorLists[l].namePartOrders.remove("InLn");
				}
			}
		}
		
		//	sort out author lists based on alignment vote
		if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Author List Styles from " + bibRefs.length + " references:");
		AuthorListStyle authorListStyle = null;
		for (Iterator alsit = authorListStyles.keySet().iterator(); alsit.hasNext();) {
			String alsKey = ((String) alsit.next());
			AuthorListStyle als = ((AuthorListStyle) authorListStyles.get(alsKey));
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) {
				System.out.println(" - " + als.key + " (" + als.instanceCount + " instances in " + als.refIDs.size() + " refs, " + als.nameCount + " names, " + als.tokenCount + " tokens):");
				System.out.print("   - bridged: ");
				for (Iterator bit = als.bridged.iterator(); bit.hasNext();) {
					String b = ((String) bit.next());
					System.out.print(b + " (" + als.bridged.getCount(b) + ")" + (bit.hasNext() ? ", " : ""));
				}
				System.out.println();
//				System.out.println("   - instances:");
//				for (int i = 0; i < als.instances.size(); i++)
//					System.out.println("     - " + ((Annotation) als.instances.get(i)).toXML());
			}
			
			//	more names than styles, void support vote (can happen with few references)
			if (als.nameCount < als.namePartOrders.size()) {
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> void support vote");
				continue;
			}
			
			//	too few references to count on redundancy, decide by distinctiveness of structure
			if (bibRefs.length < 3) {
				
				//	score by starting position (far from end)
				int startDistanceSquareSum = 0;
				int endDistanceSquareSum = 0;
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.print("   - start distances: ");
				for (Iterator sit = als.startDistances.iterator(); sit.hasNext();) {
					String s = ((String) sit.next());
					int sc = Integer.parseInt(s);
					startDistanceSquareSum -= sc;
					endDistanceSquareSum += sc;
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.print(s + " (" + als.startDistances.getCount(s) + ")" + (sit.hasNext() ? ", " : ""));
				}
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.print("   - end distances: ");
				for (Iterator sit = als.endDistances.iterator(); sit.hasNext();) {
					String e = ((String) sit.next());
					int ec = Integer.parseInt(e);
					startDistanceSquareSum += ec;
					endDistanceSquareSum -= ec;
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.print(e + " (" + als.endDistances.getCount(e) + ")" + (sit.hasNext() ? ", " : ""));
				}
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println();
				
				float startAlignmentScore = (((float) startDistanceSquareSum) / als.startDistances.elementCount());
				float endAlignmentScore = (((float) endDistanceSquareSum) / als.endDistances.elementCount());
				
				//	these things only make sense with more than one reference, as an author omission is impossible to detect in a single reference if some possible name is found
				if (bibRefs.length > 1) {
					if (als.firstNameStyles.contains("N")) {
						startAlignmentScore /= 2;
						endAlignmentScore /= 2;
					}
					if (!als.namePartOrders.contains("LnFn") && !als.namePartOrders.contains("LnIn")) {
						startAlignmentScore /= 2;
						endAlignmentScore /= 2;
					}
				}
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) {
					System.out.println("   --> score: " + startAlignmentScore);
					System.out.println("   --> score: " + endAlignmentScore);
				}
				
				als.alignmentScore = Math.max(startAlignmentScore, endAlignmentScore);
				als.isLeading = (endAlignmentScore < startAlignmentScore);
			}
			
			//	we have enough references, use vote
			else {
				
				//	score by number of times starting at same position
				int startDistanceCountSquareSum = 0;
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.print("   - start distances: ");
				for (Iterator sit = als.startDistances.iterator(); sit.hasNext();) {
					String s = ((String) sit.next());
					int sc = als.startDistances.getCount(s);
					startDistanceCountSquareSum += (sc * sc);
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.print(s + " (" + als.startDistances.getCount(s) + ")" + (sit.hasNext() ? ", " : ""));
				}
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println();
				
				float startAlignmentScore = (((float) startDistanceCountSquareSum) / als.startDistances.elementCount());
				if (als.firstNameStyles.contains("N"))
					startAlignmentScore /= 2;
				if (!als.namePartOrders.contains("LnFn") && !als.namePartOrders.contains("LnIn"))
					startAlignmentScore /= 2;
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   --> score: " + startAlignmentScore);
				
				if ((als.instanceCount * 2) < bibRefs.length) {
					startAlignmentScore = ((startAlignmentScore * als.instanceCount) / bibRefs.length);
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   --> few instance penalty, score set to: " + startAlignmentScore);
				}
				else if ((bibRefs.length * 2) < als.instanceCount) {
					startAlignmentScore = ((startAlignmentScore * bibRefs.length) / als.instanceCount);
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   --> many instance penalty, score set to: " + startAlignmentScore);
				}
				
				int endDistanceCountSquareSum = 0;
				System.out.print("   - end distances: ");
				for (Iterator eit = als.endDistances.iterator(); eit.hasNext();) {
					String e = ((String) eit.next());
					int ec = als.endDistances.getCount(e);
					endDistanceCountSquareSum += (ec * ec);
					System.out.print(e + " (" + als.endDistances.getCount(e) + ")" + (eit.hasNext() ? ", " : ""));
				}
				System.out.println();
				float endAlignmentScore = (((float) endDistanceCountSquareSum) / als.endDistances.elementCount());
				if (als.firstNameStyles.contains("N"))
					endAlignmentScore /= 2;
				if (!als.namePartOrders.contains("LnFn") && !als.namePartOrders.contains("LnIn"))
					endAlignmentScore /= 2;
				System.out.println("   --> score: " + endAlignmentScore);
				
				if ((als.instanceCount * 2) < bibRefs.length) {
					endAlignmentScore = ((endAlignmentScore * als.instanceCount) / bibRefs.length);
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   --> few instance penalty, score set to: " + endAlignmentScore);
				}
				else if ((bibRefs.length * 2) < als.instanceCount) {
					endAlignmentScore = ((endAlignmentScore * bibRefs.length) / als.instanceCount);
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   --> many instance penalty, score set to: " + endAlignmentScore);
				}
				
				als.alignmentScore = Math.max(startAlignmentScore, endAlignmentScore);
				als.isLeading = (endAlignmentScore < startAlignmentScore);
			}
			
			
			if ((als.refIDs.size() * 3) < bibRefs.length) {
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> too few references covered");
				continue;
			}
			
			if ((als.instanceCount * 3) < bibRefs.length) {
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> too few instances");
				continue;
			}
			
			if (authorListStyle == null) {
				authorListStyle = als;
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> OK for starters");
				continue;
			}
			
			if (authorListStyle.alignmentScore < als.alignmentScore) {
				authorListStyle = als;
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> new top style");
				continue;
			}
			else if (authorListStyle.alignmentScore > als.alignmentScore) {
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> worse than current style");
				continue;
			}
			
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> same as current style");
			if (als.nameCount > authorListStyle.nameCount) {
				authorListStyle = als;
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> new top style for more names");
				continue;
			}
			else if (als.nameCount < authorListStyle.nameCount) {
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> fewer names than current style");
				continue;
			}
			
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> same number of names as current style");
			if (als.namePartOrders.size() < authorListStyle.namePartOrders.size()) {
				authorListStyle = als;
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> new top style for fewer name part orders");
				continue;
			}
			else if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> same or more name part orders");
			
			//	TODO maybe also consider number of bridged tokens, fewer = better
			//	TODO if so, maybe also reward bridged _separators_, as those are normal syntax
			
			//	TODO maybe also reward constant proximity to adjacent details, with at most some separating punctuation in between
		}
		
		//	finally
		return authorListStyle;
	}
	
	private static void countAuthorListToStyle(AuthorList authorList, BibRef bibRef, int bibRefCount, LinkedHashMap authorListStyles) {
		String alsKey = AuthorListStyle.getKey(authorList);
		AuthorListStyle als = ((AuthorListStyle) authorListStyles.get(alsKey));
		if (als == null) {
			als = new AuthorListStyle(authorList);
			authorListStyles.put(als.key, als);
		}
		if (als.refIDs.add(bibRef.annotation.getAnnotationID()) || (bibRefCount >= 3)) {
//			als.instances.add(authorList.annotation);
			als.instanceCount++;
			als.nameCount += authorList.authorNames.size();
			als.tokenCount += authorList.annotation.size();
			als.startDistances.add("" + authorList.annotation.getStartIndex());
			als.endDistances.add("" + (bibRef.annotation.size() - authorList.annotation.getEndIndex()));
			als.bridged.addAll(authorList.bridged);
		}
	}
	
	private void filterAuthorLists(BibRef[] bibRefs, AuthorListStyle authorListStyle, Dictionary nameStopWords, ProgressMonitor pm) {
		if (authorListStyle == null)
			return;
		
		if (DEBUG) {
			System.out.println("Author lists style is " + authorListStyle.key + " with score " + authorListStyle.alignmentScore);
			System.out.println("Author lists alignment is " + (authorListStyle.isLeading ? "leading" : "tailing"));
		}
		
		//	for volume references, check for editor list labels, and re-select author list style if no author lists match current style
		if (bibRefs[0].parentRef != null) {
//			boolean reselectAuthorListStyle = false;
			
			//	assess editor lists based on instance counts (editor lists can and do breach sytle ...)
//			int labeledEditorListCount = 0;
//			int styleCompatibleLabeledEditorListCount = 0;
			int labeledEditorListBibRefCount = 0;
			int nonStyleCompatibleLabeledEditorListBibRefCount = 0;
			for (int r = 0; r < bibRefs.length; r++) {
				if (bibRefs[r].preExistingStructure)
					continue;
				boolean gotLabeledEditorList = false;
				boolean gotStyleCompatibleLabeledEditorList = false;
				for (int l = 0; l < bibRefs[r].authorLists.length; l++) {
					if (bibRefs[r].authorLists[l].editorListLabel != null) {
//						labeledEditorListCount++;
						gotLabeledEditorList = true;
						if (authorListStyle.isCompatible(bibRefs[r].authorLists[l])) {
							gotStyleCompatibleLabeledEditorList = true;
//							styleCompatibleLabeledEditorListCount++;
						}
					}
				}
				if (gotLabeledEditorList) {
					labeledEditorListBibRefCount++;
					if (!gotStyleCompatibleLabeledEditorList) {
//						reselectAuthorListStyle = true;
						nonStyleCompatibleLabeledEditorListBibRefCount++;
					}
				}
			}
			
			//	re-select style if necessary (more than half of labeled editor lists conflict with current style)
//			if (reselectAuthorListStyle) {
			if ((nonStyleCompatibleLabeledEditorListBibRefCount * 2) > labeledEditorListBibRefCount) {
				authorListStyle = this.getAuthorListStyle(bibRefs);
				if (DEBUG) {
					System.out.println("Reselected author list style as " + authorListStyle.key + " with score " + authorListStyle.alignmentScore);
					System.out.println("Author list alignment now is " + (authorListStyle.isLeading ? "leading" : "tailing"));
				}
			}
		}
		
		//	sort out author lists
		for (int r = 0; r < bibRefs.length; r++) {
			pm.setProgress((r * 100) / bibRefs.length);
			if (bibRefs[r].preExistingStructure)
				continue;
			
			//	filter by style, and perform mergers
			this.filterAuthorLists(bibRefs[r], authorListStyle, nameStopWords);
			
			//	filter late author lists if dealing with few references
			if ((bibRefs.length < 3) && (bibRefs[r].authorLists.length > 1)) {
				AuthorList[] fAuthorLists = {bibRefs[r].authorLists[0]};
				bibRefs[r].authorLists = fAuthorLists;
				if (DEBUG) System.out.println("  ==> reduced to " + bibRefs[r].authorLists[0].annotation.toXML());
			}
		}
	}
	
	private void filterAuthorLists(BibRef bibRef, AuthorListStyle authorListStyle, Dictionary nameStopWords) {
		if (DEBUG) System.out.println("Filtering author lists in " + bibRef.annotation.toXML());
		
		//	duplicate initials based author name lists depending on majority style (prevents misses in face of sloppy in-name punctuation, etc.)
		if ((authorListStyle.firstNameStyles.size() == 1) && authorListStyle.firstNameStyles.contains("I") && (authorListStyle.namePartOrders.size() == 1)) {
			
			//	collect what we have for duplivate prevention
			HashSet authorListKeys = new HashSet();
			for (int l = 0; l < bibRef.authorLists.length; l++) {
				String alKey = (bibRef.authorLists[l].annotation.getStartIndex() + "-" + bibRef.authorLists[l].annotation.getEndIndex() + "-" + AuthorListStyle.getKey(bibRef.authorLists[l]));
				authorListKeys.add(alKey);
			}
			
			//	create any duplicates we might need
			ArrayList authorLists = new ArrayList();
			for (int l = 0; l < bibRef.authorLists.length; l++) {
				authorLists.add(bibRef.authorLists[l]); // hold on to what we have, we filter below
				
				//	check basic conditions
				if (authorListStyle.isCompatible(bibRef.authorLists[l]))
					continue; // no reason for creating any duplicates ...
				if (bibRef.authorLists[l].isInstitutionName)
					continue; // institution names don't exhibit all the spelling variation we're dealing with here
				if (!authorListStyle.firstNameStyles.equals(bibRef.authorLists[l].firstNameStyles))
					continue; // incompatible first name styles
				
				//	check name part orders with leading last name
				if (authorListStyle.namePartOrders.contains("LnFn") || authorListStyle.namePartOrders.contains("LnIn")) {
					if (!bibRef.authorLists[l].namePartOrders.contains("LnFn") && !bibRef.authorLists[l].namePartOrders.contains("LnIn"))
						continue; // more than just a name part order mixup
					HashSet alNpos = new HashSet(bibRef.authorLists[l].namePartOrders);
					alNpos.remove("LnFn");
					alNpos.remove("LnIn");
					if (alNpos.size() != 0)
						continue; // we have other name part orders involved
				}
				
				//	check name part orders with tailing last name
				else if (authorListStyle.namePartOrders.contains("FnLn") || authorListStyle.namePartOrders.contains("InFn")) {
					if (!bibRef.authorLists[l].namePartOrders.contains("FnLn") && !bibRef.authorLists[l].namePartOrders.contains("InLn"))
						continue; // more than just a name part order mixup
					HashSet alNpos = new HashSet(bibRef.authorLists[l].namePartOrders);
					alNpos.remove("FnLn");
					alNpos.remove("InLn");
					if (alNpos.size() != 0)
						continue; // we have other name part orders involved
				}
				
				//	something's off, play it safe
				else continue;
				
				//	clone author list with adjusted style (beware of duplicates, though)
				AuthorList al = new AuthorList(bibRef.annotation, bibRef.authorLists[l].annotation, bibRef.authorLists[l].authorNames, bibRef.nobleTitleToken);
				al.namePartOrders.clear();
				al.namePartOrders.addAll(authorListStyle.namePartOrders);
				String alKey = (al.annotation.getStartIndex() + "-" + al.annotation.getEndIndex() + "-" + AuthorListStyle.getKey(al));
				if (authorListKeys.add(alKey)) {
					authorLists.add(al);
					if (DEBUG) System.out.println(" - duplicated " + AuthorListStyle.getKey(bibRef.authorLists[l]) + " as " + AuthorListStyle.getKey(al) + " " + bibRef.authorLists[l].annotation.toXML());
				}
			}
			
			//	anything new?
			if (authorLists.size() > bibRef.authorLists.length)
				bibRef.authorLists = ((AuthorList[]) authorLists.toArray(new AuthorList[authorLists.size()]));
		}
		
		//	apply basic style filter
		ArrayList authorLists = new ArrayList();
		ArrayList institutionalAuthorLists = new ArrayList();
		ArrayList knownAuthorLists = new ArrayList();
		ArrayList labeledEditorLists = new ArrayList();
		boolean gotLabeledEditorLists = false;
		for (int l = 0; l < bibRef.authorLists.length; l++) {
			if (DEBUG) System.out.println(" - " + bibRef.authorLists[l].annotation.toXML());
			if (bibRef.authorLists[l].isInstitutionName) {
				institutionalAuthorLists.add(bibRef.authorLists[l]);
				if (DEBUG) System.out.println("  ==> institution, shelved " + AuthorListStyle.getKey(bibRef.authorLists[l]));
			}
			else if (authorListStyle.isCompatible(bibRef.authorLists[l])) {
				authorLists.add(bibRef.authorLists[l]);
				if (bibRef.authorLists[l].editorListLabel != null)
					gotLabeledEditorLists = true;
				if (DEBUG) System.out.println("  ==> retained " + AuthorListStyle.getKey(bibRef.authorLists[l]));
			}
			else if (((Annotation) bibRef.authorLists[l].authorNames.get(0)).hasAttribute(knownAuthorMarker)) {
				knownAuthorLists.add(bibRef.authorLists[l]);
				if (DEBUG) System.out.println("  ==> known, shelved " + AuthorListStyle.getKey(bibRef.authorLists[l]));
			}
			else if ((bibRef.parentRef != null) && (bibRef.authorLists[l].editorListLabel != null)) {
				labeledEditorLists.add(bibRef.authorLists[l]);
				if (DEBUG) System.out.println("  ==> labeled editor list, shelved " + AuthorListStyle.getKey(bibRef.authorLists[l]));
			}
			else if (DEBUG) System.out.println("  ==> removed " + AuthorListStyle.getKey(bibRef.authorLists[l]));
		}
		
		//	use editor list label in volume references if latter present somewhere
		if (bibRef.parentRef != null) {
			
			// resort to labeled editor lists if no matching list found (must be severe style breach)
			if (authorLists.isEmpty() && (labeledEditorLists.size() != 0)) {
				authorLists.addAll(labeledEditorLists);
				gotLabeledEditorLists = true;
			}
			
			//	filter anything after labeled editor lists
			if (gotLabeledEditorLists) {
				int labeledEditorListEnd = -1;
				for (int l = 0; l < authorLists.size(); l++) {
					AuthorList editorList = ((AuthorList) authorLists.get(l));
					if (editorList.editorListLabel != null)
						labeledEditorListEnd = Math.max(labeledEditorListEnd, editorList.annotation.getEndIndex());
				}
				for (int l = 0; l < authorLists.size(); l++) {
					AuthorList editorList = ((AuthorList) authorLists.get(l));
					if (editorList.annotation.getEndIndex() > labeledEditorListEnd)
						authorLists.remove(l--);
				}
			}
		}
		
		//	resort to institution names if no author lists left (institution names match but any style)
		else if (authorLists.isEmpty()) {
			authorLists.addAll(institutionalAuthorLists);
			if (authorLists.isEmpty()) // resort to known author names if no institutions present (must be severe style breach)
				authorLists.addAll(knownAuthorLists);
		}
		
		//	filter out author lists contained in style compatible others
		for (int l = 0; l < authorLists.size(); l++) {
			AuthorList al = ((AuthorList) authorLists.get(l));
			if (DEBUG) System.out.println("Filtering inside (style equality) " + al.annotation.toXML());
			if (!isAuthorListTerminated(bibRef, al)) {
				if (DEBUG) System.out.println(" ==> non-terminated, unsafe filtering basis");
				continue;
			}
			for (int cl = (l+1); cl < authorLists.size(); cl++) {
				AuthorList cal = ((AuthorList) authorLists.get(cl));
				if (!AnnotationUtils.contains(al.annotation, cal.annotation))
					continue;
				if (al.namePartOrders.size() != cal.namePartOrders.size())
					continue;
				if (!al.namePartOrders.containsAll(cal.namePartOrders))
					continue;
				if (al.firstNameStyles.size() != cal.firstNameStyles.size())
					continue;
				if (!al.firstNameStyles.containsAll(cal.firstNameStyles))
					continue;
				if (al.initialsStyles.size() != cal.initialsStyles.size())
					continue;
				if (!al.initialsStyles.containsAll(cal.initialsStyles))
					continue;
				authorLists.remove(cl--);
				if (DEBUG) System.out.println("   - removed " + cal.annotation.toXML());
			}
		}
		
		//	TODO_not waive filter if no author lists remaining at all ??? ('Forum Herbulot' in ejt-404_brehm.pdf.imf.xml)
		if (authorLists.size() < bibRef.authorLists.length)
			bibRef.authorLists = ((AuthorList[]) authorLists.toArray(new AuthorList[authorLists.size()]));
		
		//	nothing to merge or filter ...
		if (bibRef.authorLists.length < 2)
			return;
		
		//	index existing author lists to prevent duplication
		HashSet authorListStrings = new HashSet();
		for (int l = 0; l < bibRef.authorLists.length; l++)
			authorListStrings.add(bibRef.authorLists[l].annotation.getValue());
		
		//	merge style compatibe author lists (helps bridge over broken author names)
		while (true) {
			authorLists.clear();
			int firstAuthorListEnd = bibRef.authorLists[0].annotation.getEndIndex();
			for (int l = 0; l < bibRef.authorLists.length; l++) {
				
				//	have we reached a new group of author lists, separated by some actual gap?
				if (firstAuthorListEnd < bibRef.authorLists[l].annotation.getStartIndex())
					firstAuthorListEnd = bibRef.authorLists[l].annotation.getEndIndex();
				
				//	no use merging institution names, they tend to come alone
				if (bibRef.authorLists[l].isInstitutionName) {
					authorLists.add(bibRef.authorLists[l]);
					continue;
				}
				
				//	make sure to stick with one merger per round to prevent bridging larger gaps than necessary
				if (authorLists.size() > l) {
					authorLists.add(bibRef.authorLists[l]);
					continue;
				}
				
				//	check for mergers
				if (DEBUG) System.out.println("Checking author list mergers from " + bibRef.authorLists[l].annotation.toXML());
				for (int ml = (l+1); ml < bibRef.authorLists.length; ml++) {
					if (DEBUG) System.out.println(" - checking against " + bibRef.authorLists[ml].annotation.toXML());
					if (bibRef.authorLists[ml].annotation.getStartIndex() < bibRef.authorLists[l].annotation.getEndIndex()) {
						if (DEBUG) System.out.println(" --> overlapping");
						continue; // these two are overlapping or nested, no use bridging
					}
					if (bibRef.authorLists[ml].annotation.getEndIndex() <= firstAuthorListEnd) {
						if (DEBUG) System.out.println(" --> non-extending");
						continue; // merger result already marked, no use bridging
					}
					if (bibRef.authorLists[ml].isInstitutionName) {
						if (DEBUG) System.out.println(" --> institution name");
						continue; // no use merging institution names, they tend to come alone
					}
					
					//	check bridged tokens
					String bridgedMergeBlocker = null;
					int bridgedNameSeparatorCount = 0;
					for (int t = bibRef.authorLists[l].annotation.getEndIndex(); t < bibRef.authorLists[ml].annotation.getStartIndex(); t++) {
						String toBridge = bibRef.annotation.valueAt(t);
						if (Gamta.isNumber(toBridge)) {
							bridgedMergeBlocker = toBridge;
							break; // never merge over numbers
						}
						if ((toBridge.length() == 1) && Gamta.isPunctuation(toBridge) && (".,&".indexOf(toBridge) == -1)) {
							bridgedMergeBlocker = toBridge;
							break; // don't merge over punctuation marks unlikely in author lists
						}
						if (bibRef.nameListSeparator[t]) {
							bridgedNameSeparatorCount++;
							continue;
						}
						if (Gamta.isWord(toBridge) && (toBridge.length() > 3) && toBridge.equals(toBridge.toLowerCase()) && !nameStopWords.lookup(toBridge)) {
							bridgedMergeBlocker = toBridge;
							break; // refuse merger over lower case words that are neither name stop words nor separators
						}
					}
					
					//	any counter indications?
					if (bridgedMergeBlocker != null) {
						if (DEBUG) System.out.println(" --> cannot bridge " + bridgedMergeBlocker);
						break; // no use trying further mergers from this one (sorted by increasing start index, we'd run into blocker again)
					}
//					
//					//	TODOne refuse bridging leading initials if directly before second author list
//					//	DO NOT DO THIS, NON-EXTENDING CATCH DOES THE TRICK, AND THIS MIGHT END UP PREVENTING SOME GOOD MERGERS					
//					if (authorListStyle.namePartOrders.contains("InLn") && !bibRef.authorLists[l].namePartOrders.contains("InLn") && (bibRef.authorLists[l].annotation.getEndIndex() < bibRef.authorLists[ml].annotation.getStartIndex())) {
//						Annotation gap = Gamta.newAnnotation(bibRef.annotation, "authorListGap", bibRef.authorLists[l].annotation.getEndIndex(), (bibRef.authorLists[ml].annotation.getStartIndex() - bibRef.authorLists[l].annotation.getEndIndex()));
//						if (gap.getValue().matches(".*(\\s?[A-Z]\\.)+")) {
//							if (DEBUG) System.out.println(" --> cannot bridge initials in " + gap.getValue());
//							break; // no use trying further mergers from this one (sorted by increasing start index, we'd run into blocker again)
//						}
//					}
					
					//	insist on bridging some name list separator if author lists not immediately adjacent (there has to be one at least, most likely even two if we have a broken name)
					if ((bridgedNameSeparatorCount == 0) && (bibRef.authorLists[l].annotation.getEndIndex() != bibRef.authorLists[ml].annotation.getStartIndex())) {
						if (DEBUG) System.out.println(" --> cannot bridge without name list separator");
						continue; // there might be another author list further out with a separator before it
					}
					
					//	perform merger (watch out for duplicates, though)
					Annotation mAuthorList = Gamta.newAnnotation(bibRef.annotation, AUTHOR_LIST_ANNOTATION_TYPE, bibRef.authorLists[l].annotation.getStartIndex(), (bibRef.authorLists[ml].annotation.getEndIndex() - bibRef.authorLists[l].annotation.getStartIndex()));
					if (authorListStrings.add(mAuthorList.getValue())) {
						ArrayList mAuthorNames = new ArrayList();
						mAuthorNames.addAll(bibRef.authorLists[l].authorNames);
						mAuthorNames.addAll(bibRef.authorLists[ml].authorNames);
						AuthorList mal = new AuthorList(bibRef.annotation, mAuthorList, mAuthorNames, bibRef.nobleTitleToken);
						if (bibRef.parentRef != null) {
							if (bibRef.authorLists[ml].editorListLabel != null)
								mal.editorListLabel = bibRef.authorLists[ml].editorListLabel;
							else if (bibRef.authorLists[l].editorListLabel != null)
								mal.editorListLabel = bibRef.authorLists[l].editorListLabel;
						}
						authorLists.add(mal);
						if (DEBUG) System.out.println(" --> got merged author list " + mAuthorList.toXML());
						break; // stick with one merger per left list to prevent bridging larger gaps than necessary
					}
					else if (DEBUG) System.out.println(" --> merged before");
				}
				
				//	retain original author list (sorts right after any merged one)
				authorLists.add(bibRef.authorLists[l]);
			}
			
			//	anything new?
			if (authorLists.size() > bibRef.authorLists.length)
				bibRef.authorLists = ((AuthorList[]) authorLists.toArray(new AuthorList[authorLists.size()]));
			
			//	we're done here
			else break;
		}
		
		//	eliminate author lists based upon editor list label if latter present somewhere
		authorLists.clear();
		authorLists.addAll(Arrays.asList(bibRef.authorLists));
		if ((bibRef.parentRef != null) && gotLabeledEditorLists)
			for (int l = 0; l < authorLists.size(); l++) {
				if (((AuthorList) authorLists.get(l)).editorListLabel == null)
					authorLists.remove(l--);
			}
		if (authorLists.size() < bibRef.authorLists.length)
			bibRef.authorLists = ((AuthorList[]) authorLists.toArray(new AuthorList[authorLists.size()]));
		
		//	filter out author lists contained in style compatible others
		authorLists.clear();
		authorLists.addAll(Arrays.asList(bibRef.authorLists));
		for (int l = 0; l < authorLists.size(); l++) {
			AuthorList al = ((AuthorList) authorLists.get(l));
			if (DEBUG) System.out.println("Filtering inside (style inclusion) " + al.annotation.toXML());
			if (!isAuthorListTerminated(bibRef, al)) {
				if (DEBUG) System.out.println(" ==> non-terminated, unsafe filtering basis");
				continue;
			}
			for (int cl = (l+1); cl < authorLists.size(); cl++) {
				AuthorList cal = ((AuthorList) authorLists.get(cl));
				if (!AnnotationUtils.contains(al.annotation, cal.annotation))
					continue;
//				if (al.namePartOrders.size() != cal.namePartOrders.size())
//					continue;
				if (!al.namePartOrders.containsAll(cal.namePartOrders))
					continue;
//				if (al.firstNameStyles.size() != cal.firstNameStyles.size())
//					continue;
				if (!al.firstNameStyles.containsAll(cal.firstNameStyles))
					continue;
//				if (al.initialsStyles.size() != cal.initialsStyles.size())
//					continue;
				if (!al.initialsStyles.containsAll(cal.initialsStyles))
					continue;
				authorLists.remove(cl--);
				if (DEBUG) System.out.println("   - removed " + cal.annotation.toXML());
			}
		}
		if (authorLists.size() < bibRef.authorLists.length)
			bibRef.authorLists = ((AuthorList[]) authorLists.toArray(new AuthorList[authorLists.size()]));
	}
	
	private static boolean isAuthorListTerminated(BibRef bibRef, AuthorList authorList) {
		if (authorList.annotation.getEndIndex() == bibRef.annotation.size())
			return true; // termineted by reference end
		if (isAuthorListTerminated(bibRef, authorList.annotation.getEndIndex()))
			return true;
		if ((authorList.annotation.getEndIndex() + 1) == bibRef.annotation.size())
			return true; // termineted by some stray reference end
		if (isAuthorListTerminated(bibRef, (authorList.annotation.getEndIndex() + 1)))
			return true;
		return false; // this one is unsafe both around and after end index
	}
	private static boolean isAuthorListTerminated(BibRef bibRef, int endIndex) {
		String lastValue = bibRef.annotation.valueAt(endIndex-1);
		String nextValue = bibRef.annotation.valueAt(endIndex);
		return isAuthorListTerminated(lastValue, nextValue);
	}
	private static boolean isAuthorListTerminated(String lastValue, String nextValue) {
		if ("([{".indexOf(nextValue) != -1)
			return true; // start of year in brackets following (including OCR error)
		if (".,;".indexOf(nextValue) != -1)
			return true; // classic separator following
		if (nextValue.matches("[12][0-9]{3}"))
			return true; // year following
		if (":".equals(nextValue)) {
			if (lastValue.length() > 2)
				return true; // too long for short acronym at start of title mistaken for an initial
			if (!Gamta.isWord(lastValue))
				return true; // this one is unambiguous
			return false; // let's play this one safe
		}
		//	TODO_not consider dashes??? ==> they are more frequent in double names than as reference detail separators
		if (!".".equals(lastValue))
			return false; // no terminating period, this one's unsafe (all the other options don't go _into_ author lists in the first place)
		if (nextValue.equals(nextValue.toLowerCase()))
			return false; // lower case word following, this one is unsafe
		return true; // this one is unsafe
	}
	
	private void completeAuthorLists(BibRef bibRef, int bibRefCount, NameStyle nameStyle, AuthorListStyle authorListStyle, boolean authorListLeading, boolean authorListTerminated) {
		
		//	TODO also make this work for tailing author lists !!!
		//	TODO find reference style with tailing author list in the first place
		
		//	if we have a leading, (year-) terminated author list, we can even fill in a blank
		if ((bibRef.authorList == null) && authorListLeading && authorListTerminated) {
			int authorListEnd = -1;
			
			//	find end right before year in an '<authorList> <year>' layout
			if ((bibRef.parentRef == null) && (bibRef.year != null))
				authorListEnd = bibRef.year.getStartIndex();
			
			//	find end right before editor list label in volume reference
			else if ((bibRef.parentRef != null) && (bibRef.editorListLabels.length != 0))
				authorListEnd = bibRef.editorListLabels[0].getStartIndex();
			
			//	add synthetic author list
			if (authorListEnd != -1) {
				bibRef.authorList = this.markAuthorListGap(bibRef.annotation, 0, authorListEnd);
				bibRef.authors = new Annotation[0];
			}
		}
		
		//	anything to work with?
		if ((bibRef.authorList == null) || (bibRef.authors == null))
			return;
		
		//	find earliest start and latest end of author list (defaulting to current end)
		int authorListStart = (authorListLeading ? 0 : bibRef.authorList.getStartIndex());
		int authorListEnd = bibRef.authorList.getEndIndex();
		if (authorListTerminated) {
			
			//	find end right before year in an '<authorList> <year>' layout
			if ((bibRef.parentRef == null) && (bibRef.year != null))
				authorListEnd = bibRef.year.getStartIndex();
			
			//	find end right before editor list label in volume reference
			else if ((bibRef.parentRef != null) && (bibRef.editorListLabels.length != 0))
				authorListEnd = bibRef.editorListLabels[0].getStartIndex();
		}
		
		//	mark existing author names
		boolean[] isAuthorName = createTokenFilter(bibRef.annotation, bibRef.authors);
		
		//	find gaps (if any)
		if (DEBUG) System.out.println("Seeking author list gaps in " + bibRef.annotation.toXML());
		ArrayList authorListGaps = new ArrayList();
		int authorListGapStart = -1;
		for (int t = authorListStart; t <= authorListEnd; t++) {
			if ((t == authorListEnd) || isAuthorName[t]) {
				if (authorListGapStart != -1) {
					Annotation authorListGap = this.markAuthorListGap(bibRef.annotation, authorListGapStart, t);
					if (authorListGap != null) {
						authorListGaps.add(authorListGap);
						if (DEBUG) System.out.println(" - found author list gap " + authorListGap.toXML());
					}
				}
				authorListGapStart = -1;
				continue; // we've already found this one
			}
			if (Gamta.isWord(bibRef.annotation.valueAt(t)) && (authorListGapStart == -1))
				authorListGapStart = t;
		}
		
		//	any gaps to fill?
		if (authorListGaps.isEmpty())
			return;
		
		//	remove 'et al.' gaps, and cut gaps containing 'et al.'
		for (int g = 0; g < authorListGaps.size(); g++) {
			Annotation authorListGap = ((Annotation) authorListGaps.get(g));
			for (int a = 0; a < bibRef.authorNames.length; a++) {
				if (etAlSpecialType.equals(bibRef.authorNames[a].getType()) && AnnotationUtils.liesIn(bibRef.authorNames[a], authorListGap)) {
					authorListGap = this.markAuthorListGap(bibRef.annotation, authorListGap.getStartIndex(), bibRef.authorNames[a].getStartIndex());
					if (authorListGap == null)
						authorListGaps.remove(g--);
					else authorListGaps.set(g, authorListGap);
					break;
				}
			}
		}
		
		//	any gaps to fill?
		if (authorListGaps.isEmpty())
			return;
		
		//	bridge 'and' between institution names unless it's a primary separator
		HashSet authorNameListStrings = new HashSet();
		for (int n = 0; n < bibRef.authorNames.length; n++)
			authorNameListStrings.add(bibRef.authorNames[n].getValue());
		ArrayList authorNameList = new ArrayList(Arrays.asList(bibRef.authorNames));
		for (int n = 0; n < authorNameList.size(); n++) {
			Annotation authorName = ((Annotation) authorNameList.get(n));
			if (!authorName.hasAttribute(institutionNameMarker))
				continue; // we're only interested in institution names here
			if (DEBUG) System.out.println(" - attempting to extend institution name " + authorName.toXML());
			for (int cn = (n+1); cn < authorNameList.size(); cn++) {
				Annotation cAuthorName = ((Annotation) authorNameList.get(cn));
				if (!cAuthorName.hasAttribute(institutionNameMarker))
					continue; // we're only interested in institution names here
				if (cAuthorName.getStartIndex() < authorName.getEndIndex())
					continue; // overlapping
				if ((cAuthorName.getStartIndex() - authorName.getEndIndex()) > 1)
					break; // too far apart
				if (isAuthorName[cAuthorName.getStartIndex()])
					continue; // marked before, don't bridge into already-charted territory
				if ((cAuthorName.getStartIndex() > authorName.getEndIndex()) && (authorListStyle != null)) {
					String separator = bibRef.annotation.valueAt(authorName.getEndIndex());
					int separatorCount = authorListStyle.bridged.getCount(separator);
					if (DEBUG) System.out.println("   - attempting to bridge '" + separator + "', bridged " + separatorCount + " times in " + bibRefCount + " references");
					if ((separatorCount * 5) > bibRefCount) {
						if (DEBUG) System.out.println("   ==> bridged too frequently");
						continue; // acts as separator in too many references
					}
					if (!separator.matches("(and|et|e|y|und)")) {
						if (DEBUG) System.out.println("   ==> not a conjunction");
						continue; // we're only bridging 'and' here
					}
				}
				Annotation bAuthorName = Gamta.newAnnotation(bibRef.annotation, AUTHOR_ANNOTATION_TYPE, authorName.getStartIndex(), (cAuthorName.getEndIndex() - authorName.getStartIndex()));
				bAuthorName.copyAttributes(authorName);
				if (authorNameListStrings.add(bAuthorName.getValue())) {
					authorNameList.add(n--, bAuthorName);
					if (DEBUG) System.out.println("   ==> inserted bridged author name " + bAuthorName.toXML());
					break;
				}
			}
		}
		if (bibRef.authorNames.length < authorNameList.size()) {
			Collections.sort(authorNameList, AnnotationUtils.ANNOTATION_NESTING_ORDER);
			bibRef.authorNames = ((Annotation[]) authorNameList.toArray(new Annotation[authorNameList.size()]));
		}
		
		//	try and fill gaps with previously identified author names (compatible ones first)
		ArrayList authorList = new ArrayList(Arrays.asList(bibRef.authors));
		for (int g = 0; g < authorListGaps.size(); g++) {
			Annotation authorListGap = ((Annotation) authorListGaps.get(g));
			if (DEBUG) System.out.println(" - attempting to fill gap " + authorListGap.toXML());
			
			//	find (first) style compatible author name in gap
			Annotation fillAuthorName = null;
			boolean fillAuthorNameCompatible = false;
			for (int a = 0; a < bibRef.authorNames.length; a++) {
				if (AnnotationUtils.liesIn(bibRef.authorNames[a], authorListGap)) {
					if (DEBUG) System.out.println("   - got contained name " + bibRef.authorNames[a].toXML());
					boolean authorNameCompatible = ((authorListStyle == null) || authorListStyle.isCompatible(bibRef.authorNames[a]));
					if (DEBUG) System.out.println("   - style compatible is " + authorNameCompatible);
					if ((fillAuthorName == null) || (authorNameCompatible && !fillAuthorNameCompatible)) {
						fillAuthorName = bibRef.authorNames[a];
						fillAuthorNameCompatible = authorNameCompatible;
					}
				}
				else if (authorListGap.getEndIndex() <= bibRef.authorNames[a].getStartIndex())
					break;
			}
			
			//	anything to work with?
			if (fillAuthorName == null)
				continue;
			
			//	get remaining gaps
			if (DEBUG) System.out.println("   - got gap author name " + fillAuthorName.toXML());
			Annotation gapBefore = this.markAuthorListGap(bibRef.annotation, authorListGap.getStartIndex(), fillAuthorName.getStartIndex());
			if (DEBUG && (gapBefore != null)) System.out.println("   ==> got remaining gap before " + gapBefore.toXML());
			Annotation gapAfter = this.markAuthorListGap(bibRef.annotation, fillAuthorName.getEndIndex(), authorListGap.getEndIndex());
			if (DEBUG && (gapAfter != null)) System.out.println("   ==> got remaining gap after " + gapAfter.toXML());
			
			//	reject single-token institution names unless they fill the gap completely
			if (fillAuthorName.hasAttribute(institutionNameMarker) && (fillAuthorName.size() == 1) && ((gapBefore != null) || (gapAfter != null))) {
				if (DEBUG) System.out.println("   ==> skipping single-token institution name for now " + fillAuthorName.toXML());
				continue;
			}
			
			//	add salvaged author name
			authorList.add(fillAuthorName);
			if (DEBUG) System.out.println("   ==> added author name " + fillAuthorName.toXML());
			
			//	store any remaining gaps and start over
			authorListGaps.remove(g);
			if (gapAfter != null)
				authorListGaps.add(g, gapAfter);
			if (gapBefore != null)
				authorListGaps.add(g, gapBefore);
			g--;
		}
		
		//	anything salvaged thus far?
		if (bibRef.authors.length < authorList.size()) {
			Collections.sort(authorList, AnnotationUtils.ANNOTATION_NESTING_ORDER);
			bibRef.authors = ((Annotation[]) authorList.toArray(new Annotation[authorList.size()]));
			if ((bibRef.authors[0].getStartIndex() < bibRef.authorList.getStartIndex()) || (bibRef.authorList.getEndIndex() < bibRef.authors[bibRef.authors.length - 1].getEndIndex())) {
				Annotation extAuthorList = Gamta.newAnnotation(bibRef.annotation, AUTHOR_LIST_ANNOTATION_TYPE, bibRef.authors[0].getStartIndex(), (bibRef.authors[bibRef.authors.length - 1].getEndIndex() - bibRef.authors[0].getStartIndex()));
				extAuthorList.copyAttributes(bibRef.authorList);
				bibRef.authorList = extAuthorList;
			}
			if (authorListGaps.isEmpty())
				return;
		}
		
		//	extract author list as mutable char sequence
		Annotation ala = this.markAuthorListGap(bibRef.annotation, authorListStart, authorListEnd);
		StringBuffer alb = new StringBuffer(TokenSequenceUtils.concatTokens(ala, false, true));
		StringBuffer albFixed = new StringBuffer();
		int albFixedStartOffset = bibRef.annotation.tokenAt(ala.getStartIndex()).getStartOffset();
		int albFixedEndOffset = bibRef.annotation.tokenAt(ala.getEndIndex()-1).getEndOffset();
		for (int a = 0; a < bibRef.authors.length; a++) {
			while ((albFixedStartOffset + albFixed.length()) < bibRef.authors[a].getStartOffset())
				albFixed.append('_');
			while ((albFixedStartOffset + albFixed.length()) < bibRef.authors[a].getEndOffset())
				albFixed.append('A');
		}
		while ((albFixedStartOffset + albFixed.length()) < albFixedEndOffset)
			albFixed.append('_');
		if (DEBUG) System.out.println("Original author list string is " + alb);
		if (DEBUG) System.out.println("                    meaning is " + albFixed);
		ArrayList albIndices = new ArrayList();
		for (int i = 0; i < albFixed.length(); i++)
			albIndices.add(Integer.valueOf(albFixedStartOffset + i));
		
		//	remove any dot after two or more lower case letters (abbreviated last names, typos, etc.)
		Pattern aa_dot = Pattern.compile("[a-z][a-z]\\.");
		for (Matcher m = aa_dot.matcher(alb); m.find();) {
			if (albFixed.charAt(m.start()) == 'A')
				continue;
			alb.delete((m.start() + "aa".length()), (m.start() + "aa.".length()));
			albFixed.delete((m.start() + "aa".length()), (m.start() + "aa.".length()));
			albIndices.remove(m.start() + "aa".length());
			m = aa_dot.matcher(alb); // let's be safe here, we've altered the char sequence in mid match
		}
		if (DEBUG) System.out.println("Dots after lower case eliminated to " + alb);
		if (DEBUG) System.out.println("                         meaning is " + albFixed);
		
		//	remove space between capital letters or capitalized words and sequences of lower case letters that are not in stop word dictionary (broken-up names, etc.)
		Pattern nameStart_space_aa = Pattern.compile("[A-Z][a-z]*\\s[a-z][a-z]");
		for (Matcher m = nameStart_space_aa.matcher(alb); m.find();) {
			if (albFixed.charAt(m.start()) == 'A')
				continue;
			alb.delete((m.end() - " aa".length()), (m.end() - "aa".length()));
			albFixed.delete((m.end() - " aa".length()), (m.end() - "aa".length()));
			albIndices.remove(m.end() - " aa".length());
			m = nameStart_space_aa.matcher(alb); // let's be safe here, we've altered the char sequence in mid match
		}
		if (DEBUG) System.out.println("Spaces before lower case eliminated to " + alb);
		if (DEBUG) System.out.println("                            meaning is " + albFixed);
		
		//	if NPO is 'LnIn', insert space before any terminating (sequence of) capital letters, especially if followed by dots (salvages author names with missing middle space)
		if ((authorListStyle != null) && (authorListStyle.namePartOrders.size() == 1) && authorListStyle.namePartOrders.contains("LnIn")) {
			Pattern aa_initial = Pattern.compile("[a-z][a-z][A-Z][a-z]?(\\.|\\b)");
			for (Matcher m = aa_initial.matcher(alb); m.find();) {
				if (albFixed.charAt(m.start()) == 'A')
					continue;
				alb.insert((m.start() + "aa".length()), " ");
				albFixed.insert((m.start() + "aa".length()), "_");
				albIndices.add((m.start() + "aa".length()), albIndices.get(m.start() + "aa".length()));
				m = aa_initial.matcher(alb); // let's be safe here, we've altered the char sequence in mid match
			}
			if (DEBUG) System.out.println("Spaces before initials added to " + alb);
			if (DEBUG) System.out.println("                     meaning is " + albFixed);
		}
		
		//	if FNS is 'I' and InS is 'D', append dot to every tailing or space-terminated sequence of a capital letter and at most one lower case one (salvages initials with missing dots)
		if ((authorListStyle != null) && (authorListStyle.firstNameStyles.size() == 1) && authorListStyle.firstNameStyles.contains("I") && authorListStyle.initialsStyles.contains("D")) {
			Pattern initial_noDot = Pattern.compile("[^a-zA-Z][A-Z][a-z]?[^\\.a-zA-Z]");
			for (Matcher m = initial_noDot.matcher(alb); m.find();) {
				if (albFixed.charAt(m.start()) == 'A')
					continue;
				alb.insert((m.end() - "_".length()), ".");
				albFixed.insert((m.end() - "_".length()), "_");
				albIndices.add((m.end() - "_".length()), albIndices.get(m.end() - "_".length()));
				m = nameStart_space_aa.matcher(alb); // let's be safe here, we've altered the char sequence in mid match
			}
			if (DEBUG) System.out.println("Dots after initials added to " + alb);
			if (DEBUG) System.out.println("                  meaning is " + albFixed);
		}
		
		//	get author names on corrected author list
		TokenSequence alTs = Gamta.newTokenSequence(alb, bibRef.annotation.getTokenizer());
		Annotation[] authorNames = this.getAuthorNames(alTs, null, nameStyle);
		if (DEBUG) System.out.println("Got salvaged author names:");
		for (int a = 0; a < authorNames.length; a++) {
			if (DEBUG) System.out.println(" - " + authorNames[a].toXML());
			boolean authorNameCompatible = ((authorListStyle == null) || authorListStyle.isCompatible(authorNames[a]));
			if (DEBUG) System.out.println("   style compatible is " + authorNameCompatible);
			if (authorNameCompatible) {
				int authorNameStartOffset = ((Integer) albIndices.get(authorNames[a].getStartOffset())).intValue();
				int authorNameEndOffset = (((Integer) albIndices.get(authorNames[a].getEndOffset() - 1)).intValue() + 1);
				if (DEBUG) System.out.println("   attempting to fit into gap [" + authorNameStartOffset + "," + authorNameEndOffset + ")");
				for (int g = 0; g < authorListGaps.size(); g++) {
					Annotation authorListGap = ((Annotation) authorListGaps.get(g));
					if (authorListGap.getEndOffset() <= authorNameStartOffset)
						continue; // too early
					if (authorNameEndOffset <= authorListGap.getStartOffset())
						break; // too late, we're done with this one
					if (authorNameStartOffset < authorListGap.getStartOffset())
						continue; // protrudes outside gap
					if (authorListGap.getEndOffset() < authorNameEndOffset)
						continue; // protrudes outside gap
					if (DEBUG) System.out.println("   ==> found matching gap " + authorListGap.toXML());
					
					//	find exact indices in original token sequence
					int authorStart = authorListGap.getStartIndex();
					while ((authorStart < authorListGap.getEndIndex()) && (bibRef.annotation.tokenAt(authorStart).getEndOffset() < authorNameStartOffset))
						authorStart++;
					int authorEnd = authorListGap.getEndIndex();
					while ((authorStart < authorEnd) && (authorNameEndOffset <= bibRef.annotation.tokenAt(authorEnd-1).getStartOffset()))
						authorEnd--;
					
					//	fill in author name, storing interpreted value in attribute for attribute usage
					Annotation authorName = Gamta.newAnnotation(bibRef.annotation, AUTHOR_ANNOTATION_TYPE, authorStart, (authorEnd - authorStart));
					authorName.copyAttributes(authorNames[a]);
					authorName.setAttribute("interpretedValue", authorNames[a].getValue());
					authorList.add(authorName);
					if (DEBUG) System.out.println("   ==> matched to " + authorName.toXML());
					
					//	reduce or clean up gap and proceed to next author name
					Annotation gapBefore = this.markAuthorListGap(bibRef.annotation, authorListGap.getStartIndex(), authorName.getStartIndex());
					if (DEBUG && (gapBefore != null)) System.out.println("   ==> got remaining gap before " + gapBefore.toXML());
					Annotation gapAfter = this.markAuthorListGap(bibRef.annotation, authorName.getEndIndex(), authorListGap.getEndIndex());
					if (DEBUG && (gapAfter != null)) System.out.println("   ==> got remaining gap after " + gapAfter.toXML());
					authorListGaps.remove(g);
					if (gapAfter != null)
						authorListGaps.add(g, gapAfter);
					if (gapBefore != null)
						authorListGaps.add(g, gapBefore);
					break;
				}
			}
		}
		
		//	anything salvaged via character error correction?
		if (bibRef.authors.length < authorList.size()) {
			Collections.sort(authorList, AnnotationUtils.ANNOTATION_NESTING_ORDER);
			bibRef.authors = ((Annotation[]) authorList.toArray(new Annotation[authorList.size()]));
			if ((bibRef.authors[0].getStartIndex() < bibRef.authorList.getStartIndex()) || (bibRef.authorList.getEndIndex() < bibRef.authors[bibRef.authors.length - 1].getEndIndex())) {
				Annotation extAuthorList = Gamta.newAnnotation(bibRef.annotation, AUTHOR_LIST_ANNOTATION_TYPE, bibRef.authors[0].getStartIndex(), (bibRef.authors[bibRef.authors.length - 1].getEndIndex() - bibRef.authors[0].getStartIndex()));
				extAuthorList.copyAttributes(bibRef.authorList);
				bibRef.authorList = extAuthorList;
			}
			if (authorListGaps.isEmpty())
				return;
		}
	}
	
	private Annotation markAuthorListGap(Annotation bibRef, int start, int end) {
		while ((start < end) && !Gamta.isWord(bibRef.valueAt(start)))
			start++;
		while ((start < end) && Gamta.isPunctuation(bibRef.valueAt(end-1)) && !".".equals(bibRef.valueAt(end-1)))
			end--;
		return ((start < end) ? Gamta.newAnnotation(bibRef, "authorListGap", start, (end - start)) : null);
	}
	
	private Annotation[] getYears(BibRef bibRef, boolean[] urlDoiFilter, boolean observeTitleNumbers) {
		String currentYear = new SimpleDateFormat("yyyy").format(new Date());
		//	TODO consider using year of publication instead if available (using current year as fallback)
		
		Annotation[] years = Gamta.extractAllMatches(bibRef.annotation, this.yearRegEx, false);
		ArrayList plausibleYears = new ArrayList();
		for (int y = 0; y < years.length; y++) {
			
			//	this one's in the future ...
			if (currentYear.compareTo(years[y].getValue()) < 0)
				continue;
			
			//	check if embedded in URL or DOI
			int urlDoiTokens = countFilteredTokens(years[y], urlDoiFilter);
			if (urlDoiTokens != 0)
				continue;
			
			//	check if part of title unless told to ignore
			if (observeTitleNumbers) {
				int titleNumberTokens = countFilteredTokens(years[y], bibRef.titleNumberToken);
				if (titleNumberTokens != 0)
					continue;
			}
			
			//	this one's OK
			years[y].changeTypeTo(YEAR_ANNOTATION_TYPE);
			plausibleYears.add(years[y]);
		}
		
		//	finally ...
		return ((Annotation[]) plausibleYears.toArray(new Annotation[plausibleYears.size()]));
	}
	
	private Annotation[] getPageNumbers(BibRef bibRef, boolean[] urlDoiFilter) {
		
		//	annotate tokens forbidden before page numbers
		Annotation[] pageNumberInvalidatorLeadingAnnots = Gamta.extractAllContained(bibRef.annotation, this.numberingInvalidatorsLeading, false);
		HashMap pageNumberInvalidatorsLeading = new HashMap();
		for (int i = 0; i < pageNumberInvalidatorLeadingAnnots.length; i++)
			pageNumberInvalidatorsLeading.put(new Integer(pageNumberInvalidatorLeadingAnnots[i].getStartIndex()), pageNumberInvalidatorLeadingAnnots[i]);
		
		//	annotate tokens forbidden after page numbers
		Annotation[] pageNumberInvalidatorTailingAnnots = Gamta.extractAllContained(bibRef.annotation, this.numberingInvalidatorsTailing, false);
		HashMap pageNumberInvalidatorsTailing = new HashMap();
		for (int i = 0; i < pageNumberInvalidatorTailingAnnots.length; i++)
			pageNumberInvalidatorsTailing.put(new Integer(pageNumberInvalidatorTailingAnnots[i].getStartIndex()), pageNumberInvalidatorTailingAnnots[i]);
		
		//	get candidate page numbers
		Annotation[] pageNumberAnnots = Gamta.extractAllMatches(bibRef.annotation, this.pageRegEx, false);
		ArrayList pageNumbers = new ArrayList();
		ArrayList securePageNumbers = new ArrayList();
		for (int n = 0; n < pageNumberAnnots.length; n++) {
			pageNumberAnnots[n].changeTypeTo(PAGE_NUMBER_TYPE);
			
			//	this one is actually the index number of the reference string ...
			if (pageNumberAnnots[n].getStartIndex() == 0)
				continue;
			
			//	this one is part of some range, do not mark separately
			if ((pageNumberAnnots[n].getStartIndex() != 0) && "-".equals(bibRef.annotation.valueAt(pageNumberAnnots[n].getStartIndex() - 1)))
				continue;
			else if ((pageNumberAnnots[n].getEndIndex() < bibRef.annotation.size()) && "-".equals(bibRef.annotation.valueAt(pageNumberAnnots[n].getEndIndex())))
				continue;
			
			//	this one is secure
			if (!Gamta.isNumber(pageNumberAnnots[n].firstValue())) {
				pageNumbers.add(pageNumberAnnots[n]);
				securePageNumbers.add(pageNumberAnnots[n]);
				continue;
			}
			
			//	check if embedded in URL or DOI
			int urlDoiTokens = countFilteredTokens(pageNumberAnnots[n], urlDoiFilter);
			if (urlDoiTokens != 0)
				continue;
			
			//	check if part of title
			int titleNumberTokens = countFilteredTokens(pageNumberAnnots[n], bibRef.titleNumberToken);
			if (titleNumberTokens != 0)
				continue;
			
			//	check if page number invalidated by token before it
			Annotation invalidatorLeading = ((Annotation) pageNumberInvalidatorsLeading.get(new Integer(pageNumberAnnots[n].getStartIndex()-1)));
			if (invalidatorLeading != null)
				continue;
			
			//	check if page number invalidated by token after it
			Annotation invalidatorTailing = ((Annotation) pageNumberInvalidatorsTailing.get(new Integer(pageNumberAnnots[n].getEndIndex())));
			if (invalidatorTailing == null) {
				markElectronicPaginations(pageNumberAnnots[n]);
				if (pageNumberAnnots[n].firstValue().toLowerCase().startsWith("p"))
					pageNumberAnnots[n].setAttribute("labeled");
				pageNumbers.add(pageNumberAnnots[n]);
			}
			
			//	remember info to referenced publication being a book
			else if (this.bookContentInfoNumberingInvalidatorsTailing.containsIgnoreCase(invalidatorTailing.getValue())) {
				if (DEBUG) System.out.println("Found book content info: " + pageNumberAnnots[n] + " " + invalidatorTailing);
				bibRef.bookContentInfos.add(Gamta.newAnnotation(bibRef.annotation, BOOK_CONTENT_INFO_ANNOTATION_TYPE, pageNumberAnnots[n].getStartIndex(), (invalidatorTailing.getEndIndex() - pageNumberAnnots[n].getStartIndex())));
			}
		}
		
		//	add page numbers for electronic publications
		pageNumberAnnots = Gamta.extractAllMatches(bibRef.annotation, this.ePageRegEx, false);
		for (int n = 0; n < pageNumberAnnots.length; n++) {
			pageNumberAnnots[n].changeTypeTo(PAGE_NUMBER_TYPE);
			
			//	this one is actually the index number of the reference string ...
			if (pageNumberAnnots[n].getStartIndex() == 0)
				continue;
			
			//	this one is part of some range, do not mark separately
			if ((pageNumberAnnots[n].getStartIndex() != 0) && "-".equals(bibRef.annotation.valueAt(pageNumberAnnots[n].getStartIndex() - 1)))
				continue;
			else if ((pageNumberAnnots[n].getEndIndex() < bibRef.annotation.size()) && "-".equals(bibRef.annotation.valueAt(pageNumberAnnots[n].getEndIndex())))
				continue;
			
			//	check if embedded in URL or DOI
			int urlDoiTokens = countFilteredTokens(pageNumberAnnots[n], urlDoiFilter);
			if (urlDoiTokens != 0)
				continue;
			
			//	check if part of title
			int titleNumberTokens = countFilteredTokens(pageNumberAnnots[n], bibRef.titleNumberToken);
			if (titleNumberTokens != 0)
				continue;
			
			//	this one is secure
			markElectronicPaginations(pageNumberAnnots[n]);
			if (Gamta.isNumber(pageNumberAnnots[n].firstValue()))
				pageNumbers.add(pageNumberAnnots[n]);
			else  {
				pageNumbers.add(pageNumberAnnots[n]);
				securePageNumbers.add(pageNumberAnnots[n]);
			}
		}
		
		//	we have labelled page numbers, return only those
		if (!securePageNumbers.isEmpty() && (securePageNumbers.size() < pageNumbers.size()))
			return ((Annotation[]) securePageNumbers.toArray(new Annotation[securePageNumbers.size()]));
		
		//	we have only plain page numbers
		else return ((Annotation[]) pageNumbers.toArray(new Annotation[pageNumbers.size()]));
	}
	
	private Annotation[] getPageRanges(BibRef bibRef, boolean[] urlDoiFilter) {
		Annotation[] pageRanges =  this.getArabicPageRanges(bibRef, urlDoiFilter);
		if (pageRanges.length == 0)
			pageRanges = this.getRomanPageRanges(bibRef, urlDoiFilter);
		return pageRanges;
	}
	
	private Annotation[] getArabicPageRanges(BibRef bibRef, boolean[] urlDoiFilter) {
		Annotation[] pageRangeAnnots = Gamta.extractAllMatches(bibRef.annotation, this.pageRangeArabicRegEx, false);
		ArrayList pageRanges = new ArrayList();
		for (int r = 0; r < pageRangeAnnots.length; r++) {
			if (DEBUG) System.out.println("Checking possible page range: " + pageRangeAnnots[r].getValue());
			
			//	check if embedded in URL or DOI
			int urlDoiTokens = countFilteredTokens(pageRangeAnnots[r], urlDoiFilter);
			if (urlDoiTokens != 0) {
				if (DEBUG) System.out.println(" --> overlaps with URL/DOI, ignoring");
				continue;
			}
			
			//	check overlap with title numbers
			int titleNumberTokens = countFilteredTokens(pageRangeAnnots[r], bibRef.titleNumberToken);
			if (titleNumberTokens != 0) {
				if (DEBUG) System.out.println(" --> overlaps with title number, ignoring");
				continue;
			}
			
			//	check if second number larger than first (numbers with dashes can also occur in identifiers, etc.)
			String firstNumber = null;
			String secondNumber = null;
			for (int t = 0; t < pageRangeAnnots[r].size(); t++)
				if (Gamta.isNumber(pageRangeAnnots[r].valueAt(t))) {
					if (firstNumber == null)
						firstNumber = pageRangeAnnots[r].valueAt(t);
					else if (secondNumber == null)
						secondNumber = pageRangeAnnots[r].valueAt(t);
				}
			
			//	too few numbers
			if (secondNumber == null) {
				if (DEBUG) System.out.println(" --> second number invalid");
				continue;
			}
			
			//	fill in omitted positions in second number
			if (secondNumber.length() < firstNumber.length())
				secondNumber = (firstNumber.substring(0, (firstNumber.length() - secondNumber.length())) + secondNumber);
			
			//	do we have a label?
			boolean pageRangeLabeled = pageRangeAnnots[r].firstValue().toLowerCase().startsWith("p");
			
			//	compare numerically (allow equality, as there are reference style guides and bibliography generators that apparently insist on first and last page)
			if (Integer.parseInt(secondNumber) < Integer.parseInt(firstNumber)) {
				if (!pageRangeLabeled) {
					if (DEBUG) System.out.println(" --> second number less than first");
					continue;
				}
				if (DEBUG) System.out.println(" --> second number less than first, retained for label");
			}
			
			//	this one's OK
			pageRangeAnnots[r].changeTypeTo(PAGE_RANGE_ANNOTATION_TYPE);
			markElectronicPaginations(pageRangeAnnots[r]);
			if (pageRangeLabeled)
				pageRangeAnnots[r].setAttribute("labeled");
			pageRanges.add(pageRangeAnnots[r]);
			if (DEBUG) System.out.println(" ==> got candidate page range: " + pageRangeAnnots[r].toXML());
		}
		
		return ((Annotation[]) pageRanges.toArray(new Annotation[pageRanges.size()]));
	}
	
	private Annotation[] getRomanPageRanges(BibRef bibRef, boolean[] urlDoiFilter) {
		Annotation[] pageRangeAnnots = Gamta.extractAllMatches(bibRef.annotation, this.pageRangeRomanRegEx, false);
		ArrayList pageRanges = new ArrayList();
		for (int r = 0; r < pageRangeAnnots.length; r++) {
			
			//	check if embedded in URL or DOI
			int urlDoiTokens = countFilteredTokens(pageRangeAnnots[r], urlDoiFilter);
			if (urlDoiTokens != 0)
				continue;
			
			//	check if second number larger than first (numbers with dashes can also occur in identifiers, etc.)
			String firstNumber = null;
			String secondNumber = null;
			for (int t = 0; t < pageRangeAnnots[r].size(); t++)
				if (pageRangeAnnots[r].valueAt(t).matches(this.romanNumberRegEx)) {
					if (firstNumber == null)
						firstNumber = pageRangeAnnots[r].valueAt(t);
					else if (secondNumber == null)
						secondNumber = pageRangeAnnots[r].valueAt(t);
				}
			
			//	got two numbers?
			if (secondNumber != null) try {
				
				//	compare numerically
				if (Gamta.parseRomanNumber(secondNumber) <= Gamta.parseRomanNumber(firstNumber))
					continue;
				
				//	this one's OK
				pageRangeAnnots[r].changeTypeTo(PAGE_RANGE_ANNOTATION_TYPE);
				pageRanges.add(pageRangeAnnots[r]);
			}
			
			//	we have to catch that number format exception, just in case ...
			catch (Exception e) {}
		}
		
		//	finally ...
		return ((Annotation[]) pageRanges.toArray(new Annotation[pageRanges.size()]));
	}
	
	private static void markElectronicPaginations(Annotation pagination) {
		if ("e".equals(pagination.firstValue()))
			pagination.setAttribute("e");
	}
	
	private void markTitleNumbers(BibRef bibRef) {
		bibRef.titleNumberToken = new boolean[bibRef.annotation.size()];
		Arrays.fill(bibRef.titleNumberToken, false);
		for (int p = 0; p < this.titleNumberPatterns.size(); p++) {
			Annotation[] titleNumberAnnots = Gamta.extractAllMatches(bibRef.annotation, this.titleNumberPatterns.get(p), false);
			augmentFilteredTokens(bibRef.titleNumberToken, titleNumberAnnots, null);
			if (DEBUG) {
				for (int t = 0; t < titleNumberAnnots.length; t++)
					System.out.println("Got title number [ " + this.titleNumberPatterns.get(p) + " ]: " + titleNumberAnnots[t].getValue());
			}
		}
	}
	
	private Annotation[] getLabeledDates(Annotation bibRef) {
		
		//	get and index date components
		AnnotationIndex datePartIndex = new AnnotationIndex();
		Annotation[] days = Gamta.extractAllContained(bibRef, this.dateDays, false);
		datePartIndex.addAnnotations(days, "day");
		Annotation[] months = Gamta.extractAllContained(bibRef, this.dateMonths, false);
		datePartIndex.addAnnotations(months, "month");
		Annotation[] years = Gamta.extractAllMatches(bibRef, "((199[0-9])|(2[0-9]{3}))"); // URL access dates before 1990 are somewhat unlikely ...
		datePartIndex.addAnnotations(years, "year");
		
		//	tag and index date labels ('accessed', 'published online', etc.)
		Annotation[] dateLabels = Gamta.extractAllContained(bibRef, this.dateLabels, false);
		datePartIndex.addAnnotations(dateLabels, "label");
		
		//	tag dates TODO add other formats as they occur
		ArrayList dateList = new ArrayList();
		Annotation[] dates;
		dates = AnnotationPatternMatcher.getMatches(bibRef, datePartIndex, "<label>? <day> <month> <year>");
		dateList.addAll(Arrays.asList(dates));
		dates = AnnotationPatternMatcher.getMatches(bibRef, datePartIndex, "<label>? <month> <day> <year>");
		dateList.addAll(Arrays.asList(dates));
		
		//	finally ...
		Collections.sort(dateList, AnnotationUtils.ANNOTATION_NESTING_ORDER);
		return ((Annotation[]) dateList.toArray(new Annotation[dateList.size()]));
	}
	
	private Annotation[] getDates(Annotation bibRef) {
		
		//	get and index date components
		AnnotationIndex datePartIndex = new AnnotationIndex();
		Annotation[] days = Gamta.extractAllContained(bibRef, this.dateDays, false);
		datePartIndex.addAnnotations(days, "day");
		Annotation[] months = Gamta.extractAllContained(bibRef, this.dateMonths, false);
		datePartIndex.addAnnotations(months, "month");
		Annotation[] years = Gamta.extractAllMatches(bibRef, "((1[5-9][0-9]{2})|(2[0-9]{3}))");
		datePartIndex.addAnnotations(years, "year");
		
		//	tag dates TODO add other formats as they occur
		ArrayList dateList = new ArrayList();
		Annotation[] dates;
		dates = AnnotationPatternMatcher.getMatches(bibRef, datePartIndex, "<day> <month> ','? <year>");
		dateList.addAll(Arrays.asList(dates));
		dates = AnnotationPatternMatcher.getMatches(bibRef, datePartIndex, "<month> <day> ','? <year>");
		dateList.addAll(Arrays.asList(dates));
		
		//	finally ...
		Collections.sort(dateList, AnnotationUtils.ANNOTATION_NESTING_ORDER);
		return ((Annotation[]) dateList.toArray(new Annotation[dateList.size()]));
	}
	
	private Annotation[] getPartDesignators(BibRef bibRef, boolean[] urlDoiFilter) {
		
		//	annotate tokens forbidden before part designators
		Annotation[] partDesignatorInvalidatorLeadingAnnots = Gamta.extractAllContained(bibRef.annotation, this.numberingInvalidatorsLeading, false);
		HashMap partDesignatorInvalidatorsLeading = new HashMap();
		for (int i = 0; i < partDesignatorInvalidatorLeadingAnnots.length; i++)
			partDesignatorInvalidatorsLeading.put(new Integer(partDesignatorInvalidatorLeadingAnnots[i].getStartIndex()), partDesignatorInvalidatorLeadingAnnots[i]);
		
		//	annotate tokens forbidden after part designators
		Annotation[] partDesignatorInvalidatorTailingAnnots = Gamta.extractAllContained(bibRef.annotation, this.numberingInvalidatorsTailing, false);
		HashMap partDesignatorInvalidatorsTailing = new HashMap();
		for (int i = 0; i < partDesignatorInvalidatorTailingAnnots.length; i++)
			partDesignatorInvalidatorsTailing.put(new Integer(partDesignatorInvalidatorTailingAnnots[i].getStartIndex()), partDesignatorInvalidatorTailingAnnots[i]);
		
		//	find first actual word (part designators hardly ever occur at the start, or even before the journal name)
		int firstWordIndex = 0;
		for (; firstWordIndex < bibRef.annotation.size(); firstWordIndex++) {
			String token = bibRef.annotation.valueAt(firstWordIndex);
			if ((token.length() > 1) && Gamta.isWord(token))
				break;
		}
		
		//	get part designators
		Annotation[] partDesignatorAnnots = Gamta.extractAllMatches(bibRef.annotation, this.partDesignatorRegEx, false);
		ArrayList partDesignators = new ArrayList();
		ArrayList securePartDesignators = new ArrayList();
		for (int p = 0; p < partDesignatorAnnots.length; p++) {
			if (DEBUG) System.out.println("Found possible part designator: " + partDesignatorAnnots[p].getValue());
			
			//	this one is likely a reference number, not a part designator
			//	TODO TEST Gleicher-2011-Visual comparison for information visualization.pdf (FFB7FFEAFFAFFFA5FF9FFF8F48577C63)
			//	TODO optionally (style parameter) handle '<volume>.<issue>' part designators
			//	TODO TEST Peckhamia (FFE8FFB47A43FFC5FFABFFC3FFC2FFAA)
			if (partDesignatorAnnots[p].getStartIndex() < firstWordIndex) {
				if (DEBUG) System.out.println(" --> at start, ignoring");
				continue;
			}
			
			//	this one is likely an e-publication page number, not a part designator
			if ((partDesignatorAnnots[p].getStartIndex() != 0) && "e".equals(bibRef.annotation.valueAt(partDesignatorAnnots[p].getStartIndex()-1))) {
				if (DEBUG) System.out.println(" --> e-publication page number, ignoring");
				continue;
			}
			
			//	set annotation type
			partDesignatorAnnots[p].changeTypeTo(PART_DESIGNATOR_ANNOTATION_TYPE);
//			
//			//	this one is part of some range, do not mark separately
//			//	TODOne apply this filter only later, we need these ones for number detail block issue ranges
//			if ("-".equals(bibRef.annotation.valueAt(partDesignatorAnnots[p].getStartIndex() - 1))) {
//				if (DEBUG) System.out.println(" --> after dash, ignoring");
//				continue;
//			}
//			else if ((partDesignatorAnnots[p].getEndIndex() < bibRef.annotation.size()) && "-".equals(bibRef.annotation.valueAt(partDesignatorAnnots[p].getEndIndex()))) {
//				if (DEBUG) System.out.println(" --> before dash, ignoring");
//				continue;
//			}
			
			//	check if embedded in URL or DOI
			int urlDoiTokens = countFilteredTokens(partDesignatorAnnots[p], urlDoiFilter);
			if (urlDoiTokens != 0) {
				if (DEBUG) System.out.println(" --> in URL/DOI, ignoring");
				continue;
			}
			
			//	check if part of title
			int titleNumberTokens = countFilteredTokens(partDesignatorAnnots[p], bibRef.titleNumberToken);
			if (titleNumberTokens != 0) {
				if (DEBUG) System.out.println(" --> title number, ignoring");
				continue;
			}
			
			//	this one is secure
			if (!Gamta.isNumber(partDesignatorAnnots[p].firstValue()) && !Gamta.isRomanNumber(partDesignatorAnnots[p].firstValue()) && (partDesignatorAnnots[p].firstValue().length() > 1)) {
				partDesignators.add(partDesignatorAnnots[p]);
				securePartDesignators.add(partDesignatorAnnots[p]);
				if (DEBUG) System.out.println(" ==> secure part designator");
				continue;
			}
			
			//	check if part designators invalidated by token before it
			Annotation invalidatorLeading = ((Annotation) partDesignatorInvalidatorsLeading.get(new Integer(partDesignatorAnnots[p].getStartIndex()-1)));
			if (invalidatorLeading != null) {
				if (DEBUG) System.out.println(" --> invalidated by leading '" + bibRef.annotation.valueAt(partDesignatorAnnots[p].getStartIndex()-1) + "'");
				continue;
			}
			
			//	check if part designators invalidated by token after it
			Annotation invalidatorTailing = ((Annotation) partDesignatorInvalidatorsTailing.get(new Integer(partDesignatorAnnots[p].getEndIndex())));
			if (invalidatorTailing != null) {
				if (DEBUG) System.out.println(" --> invalidated by tailing '" + bibRef.annotation.valueAt(partDesignatorAnnots[p].getEndIndex()) + "'");
				
				//	remember hint to referenced publication being a book
				if (this.bookContentInfoNumberingInvalidatorsTailing.containsIgnoreCase(invalidatorTailing.getValue())) {
					if (DEBUG) System.out.println("Found book content info: " + partDesignatorAnnots[p] + " " + invalidatorTailing);
					bibRef.bookContentInfos.add(Gamta.newAnnotation(bibRef.annotation, BOOK_CONTENT_INFO_ANNOTATION_TYPE, partDesignatorAnnots[p].getStartIndex(), (invalidatorTailing.getEndIndex() - partDesignatorAnnots[p].getStartIndex())));
				}
				continue;
			}
			
			//	ignore unlabeled letters and Roman numbers
			if (!Gamta.isNumber(partDesignatorAnnots[p].firstValue()) && !Gamta.isRomanNumber(partDesignatorAnnots[p].firstValue())) {
				if (DEBUG) System.out.println(" --> ingored as standalone letter");
				continue;
			}
			
			//	hold on to this one
			if (DEBUG) System.out.println(" ==> possible part designator");
			partDesignators.add(partDesignatorAnnots[p]);
		}
		
		//	we have labelled part designators, return only those
		if (!securePartDesignators.isEmpty() && (securePartDesignators.size() < partDesignators.size()))
			partDesignatorAnnots = ((Annotation[]) securePartDesignators.toArray(new Annotation[securePartDesignators.size()]));
		
		//	we have only plain part designators
		else partDesignatorAnnots = ((Annotation[]) partDesignators.toArray(new Annotation[partDesignators.size()]));
//		
//		//	make sure numerical part designators are preferred over letters in structure vote
//		Arrays.sort(partDesignatorAnnots, new Comparator() {
//			public int compare(Object o1, Object o2) {
//				Annotation pd1 = ((Annotation) o1);
//				Annotation pd2 = ((Annotation) o2);
//				if (Gamta.isNumber(pd1.lastValue()) == Gamta.isNumber(pd2.lastValue()))
//					return pd1.compareTo(pd2);
//				else if (Gamta.isNumber(pd1.lastValue()))
//					return -1;
//				else return 1;
//			}
//		});
		
		//	finally ...
		return partDesignatorAnnots;
	}
	
	private Annotation[] getNumberDetailBlocks(BibRef bibRef) {
		
		//	index part designators, page numbers, and page ranges
		AnnotationIndex numberIndex = new AnnotationIndex();
		boolean noPartDesignators = true;
		boolean noPaginations = true;
		if (bibRef.partDesignators != null) {
			numberIndex.addAnnotations(bibRef.partDesignators, "part");
			noPartDesignators = (bibRef.partDesignators.length == 0);
		}
		if (bibRef.pageNumbers != null) {
			numberIndex.addAnnotations(bibRef.pageNumbers, "page");
			noPaginations = (noPaginations && (bibRef.pageNumbers.length == 0));
		}
		if (bibRef.pageRanges != null) {
			numberIndex.addAnnotations(bibRef.pageRanges, "pageRange");
			noPaginations = (noPaginations && (bibRef.pageNumbers.length == 0));
		}
		if (bibRef.years != null)
			numberIndex.addAnnotations(bibRef.years, "year");
		
		//	anything to work with?
		if (noPartDesignators || noPaginations)
			return new Annotation[0];
		
		//	annotate sub part designators
		Annotation[] subPartDesignators;
		subPartDesignators = AnnotationPatternMatcher.getMatches(bibRef.annotation, numberIndex, "'(' \"[a-z]{2,4}\\\\.?\" <part>@:part ')'");
		numberIndex.addAnnotations(subPartDesignators, "subPart");
		subPartDesignators = AnnotationPatternMatcher.getMatches(bibRef.annotation, numberIndex, "',' \"[a-z]{2,4}\\\\.?\" <part>@:part");
		numberIndex.addAnnotations(subPartDesignators, "subPart");
//		subPartDesignators = AnnotationPatternMatcher.getMatches(bibRef.annotation, numberIndex, "'(' <part>@:firstPart ('-'|'/'|\"[a-z]{1,4}\\\\.?\") <part>@:lastPart ')'");
//		numberIndex.addAnnotations(subPartDesignators, "subPart");
		
		//	tag part designator and punctuation blocks TODO add other formats as they occur
		ArrayList ndBlockList = new ArrayList();
		Annotation[] ndBlocks;
		
		//	no issue number in parentheses, only accept e-page or page range
		ndBlocks = AnnotationPatternMatcher.getMatches(bibRef.annotation, numberIndex, "(('(' <year>@:yearLead ')' ','?)|(<year>@:yearLead ','))? <part>@:part @:volume <subPart>?@:subPart @(./@part):issue ((','? '(' <year>@:yearMid ')')|(',' <year>@:yearMid))? (':'|',') 'e'? <pageRange>@:pagination ((','? '(' <year>@:yearTail ')')|(',' <year>@:yearTail))?");
		ndBlocks = finishNumberDetailBlocks(ndBlocks);
		ndBlockList.addAll(Arrays.asList(ndBlocks));
		ndBlocks = AnnotationPatternMatcher.getMatches(bibRef.annotation, numberIndex, "(('(' <year>@:yearLead ')' ','?)|(<year>@:yearLead ','))? <part>@:part @:volume <subPart>?@:subPart @(./@part):issue ((','? '(' <year>@:yearMid ')')|(',' <year>@:yearMid))? (':'|',') 'e'? <page test=\"(./@e)\">@:pagination ((','? '(' <year>@:yearTail ')')|(',' <year>@:yearTail))?");
		ndBlocks = finishNumberDetailBlocks(ndBlocks);
		ndBlockList.addAll(Arrays.asList(ndBlocks));
		ndBlocks = AnnotationPatternMatcher.getMatches(bibRef.annotation, numberIndex, "(('(' <year>@:yearLead ')' ','?)|(<year>@:yearLead ','))? <part>@:part @:volume <subPart>@:subPart @(./@part):issue ((','? '(' <year>@:yearMid ')')|(',' <year>@:yearMid))? (':'|',') <page>@:pagination ((','? '(' <year>@:yearTail ')')|(',' <year>@:yearTail))?");
		ndBlocks = finishNumberDetailBlocks(ndBlocks);
		ndBlockList.addAll(Arrays.asList(ndBlocks));
		ndBlocks = AnnotationPatternMatcher.getMatches(bibRef.annotation, numberIndex, "(('(' <year>@:yearLead ')' ','?)|(<year>@:yearLead ','))? <part>@:part @:volume ((','? '(' <year>@:yearMid ')')|(',' <year>@:yearMid))? ':' <page>@:pagination ((','? '(' <year>@:yearTail ')')|(',' <year>@:yearTail))?");
		ndBlocks = finishNumberDetailBlocks(ndBlocks);
		ndBlockList.addAll(Arrays.asList(ndBlocks));
		ndBlocks = AnnotationPatternMatcher.getMatches(bibRef.annotation, numberIndex, "(('(' <year>@:yearLead ')' ','?)|(<year>@:yearLead ',')) <part>@:part @:volume <subPart>?@:subPart @(./@part):subPartDes (':'|',')? 'e'? (<page>|<pageRange>)@:pagination");
		ndBlocks = finishNumberDetailBlocks(ndBlocks);
		ndBlockList.addAll(Arrays.asList(ndBlocks));
		ndBlocks = AnnotationPatternMatcher.getMatches(bibRef.annotation, numberIndex, "<part>@:part @:volume <subPart>?@:subPart @(./@part):subPartDes ((','? '(' <year>@:yearMid ')')|(',' <year>@:yearMid)) (':'|',')? 'e'? (<page>|<pageRange>)@:pagination");
		ndBlocks = finishNumberDetailBlocks(ndBlocks);
		ndBlockList.addAll(Arrays.asList(ndBlocks));
		ndBlocks = AnnotationPatternMatcher.getMatches(bibRef.annotation, numberIndex, "<part>@:part @:volume <subPart>?@:subPart @(./@part):subPartDes (':'|',')? 'e'? (<page>|<pageRange>)@:pagination ((','? '(' <year>@:yearTail ')')|(',' <year>@:yearTail))");
		ndBlocks = finishNumberDetailBlocks(ndBlocks);
		ndBlockList.addAll(Arrays.asList(ndBlocks));
		
		//	single issue number or issue range in parentheses, accept absence of separator punctuation
		ndBlocks = AnnotationPatternMatcher.getMatches(bibRef.annotation, numberIndex, "(('(' <year>@:yearLead ')' ','?)|(<year>@:yearLead ','))? (<part>@:volume '(' <part>@:issue ')')@:part <subPart>?@:subPart @(./@part):subPartDes ((','? '(' <year>@:yearMid ')')|(',' <year>@:yearMid))? (':'|',')? 'e'? (<page>|<pageRange>)@:pagination ((','? '(' <year>@:yearTail ')')|(',' <year>@:yearTail))?");
		ndBlocks = finishNumberDetailBlocks(ndBlocks);
		ndBlockList.addAll(Arrays.asList(ndBlocks));
		ndBlocks = AnnotationPatternMatcher.getMatches(bibRef.annotation, numberIndex, "(('(' <year>@:yearLead ')' ','?)|(<year>@:yearLead ','))? (<part>@:volume ',' <part>@:issue)@:part <subPart>?@:subPart @(./@part):subPartDes ((','? '(' <year>@:yearMid ')')|(',' <year>@:yearMid))? (':'|',')? 'e'? (<page>|<pageRange>)@:pagination ((','? '(' <year>@:yearTail ')')|(',' <year>@:yearTail))?");
		ndBlocks = finishNumberDetailBlocks(ndBlocks);
		ndBlockList.addAll(Arrays.asList(ndBlocks));
		ndBlocks = AnnotationPatternMatcher.getMatches(bibRef.annotation, numberIndex, "(('(' <year>@:yearLead ')' ','?)|(<year>@:yearLead ','))? (<part>@:volume '(' (<part> ('-'|'/'|\"[a-z]{1,4}\") <part>)@:issue ')')@:part <subPart>?@:subPart @(./@part):subPartDes ((','? '(' <year>@:yearMid ')')|(',' <year>@:yearMid))? (':'|',')? 'e'? (<page>|<pageRange>)@:pagination ((','? '(' <year>@:yearTail ')')|(',' <year>@:yearTail))?");
		ndBlocks = finishNumberDetailBlocks(ndBlocks);
		ndBlockList.addAll(Arrays.asList(ndBlocks));
		
		if (DEBUG) {
			System.out.println("Number detail blocks:");
			for (int b = 0; b < ndBlockList.size(); b++)
				System.out.println(" - " + ((Annotation) ndBlockList.get(b)).toXML());
		}
		
		//	eliminate duplicates (only actual duplicates for now, we need the sub matches for the vote)
		Collections.sort(ndBlockList, AnnotationUtils.ANNOTATION_NESTING_ORDER);
		for (int b = 0; b < ndBlockList.size(); b++) {
			Annotation ndBlock = ((Annotation) ndBlockList.get(b));
			String ndOrder = ((String) ndBlock.getAttribute("ndo"));
			for (int cb = (b+1); cb < ndBlockList.size(); cb++) {
				Annotation cNdBlock = ((Annotation) ndBlockList.get(cb));
				String cNdOrder = ((String) cNdBlock.getAttribute("ndo"));
				if (AnnotationUtils.liesIn(cNdBlock, ndBlock) && ndOrder.equals(cNdOrder))
					ndBlockList.remove(cb--);
				else if (ndBlock.getEndIndex() <= cNdBlock.getStartIndex())
					break;
			}
		}
		
		//	finally ...
		return ((Annotation[]) ndBlockList.toArray(new Annotation[ndBlockList.size()]));
	}
	
	private static Annotation[] finishNumberDetailBlocks(Annotation[] numberDetailBlocks) {
		/* TODO
Also secure blocks better, adding second, punctuation-aware signature:
==> better backing for actual "<volume>, <pageNumber>" instances
==> better filtering for phony ones
==> keep some fuzziness, though, as colon in "<volume> (<issue>): <pagination>" might be lacking occasionally (one instance in test set)
  ==> maybe simply be lenient about punctuation if number block covers three or more individual numbers

Observe in the long haul if any of these rules does more harm than good !!!
		 */
		ArrayList numberDetailBlockList = new ArrayList();
		for (int b = 0; b < numberDetailBlocks.length; b++) {
			int yearCount = 0;
			StringBuffer numberDetailOrder = new StringBuffer();
//			StringBuffer punctNumberDetailOrder = new StringBuffer();
//			int punctTokenIndex = 0;
			if (numberDetailBlocks[b].hasAttribute("yearLead")) {
				numberDetailBlocks[b].setAttribute("year", numberDetailBlocks[b].getAttribute("yearLead"));
				numberDetailOrder.append("year ");
				yearCount++;
			}
			numberDetailOrder.append("part");
			if (numberDetailBlocks[b].hasAttribute("yearMid")) {
				numberDetailBlocks[b].setAttribute("year", numberDetailBlocks[b].getAttribute("yearMid"));
				numberDetailOrder.append(" year");
				yearCount++;
			}
			numberDetailOrder.append(" page");
			if (numberDetailBlocks[b].hasAttribute("yearTail")) {
				numberDetailBlocks[b].setAttribute("year", numberDetailBlocks[b].getAttribute("yearTail"));
				numberDetailOrder.append(" year");
				yearCount++;
			}
			numberDetailBlocks[b].setAttribute("ndo", numberDetailOrder.toString());
			if (yearCount < 2)
				numberDetailBlockList.add(numberDetailBlocks[b]);
		}
		if (numberDetailBlockList.size() < numberDetailBlocks.length)
			return ((Annotation[]) numberDetailBlockList.toArray(new Annotation[numberDetailBlockList.size()]));
		else return numberDetailBlocks;
	}
//	
//	private static int findEndOfNumberDetail(TokenSequence tokens, String numberDetail, int fromIndex) {
//		TokenSequence ndTokens = Gamta.newTokenSequence(numberDetail, tokens.getTokenizer());
//		int ndTokenIndex = TokenSequenceUtils.indexOf(tokens, ndTokens, fromIndex);
//		return ((ndTokenIndex == -1) ? ndTokenIndex : (ndTokenIndex + ndTokens.size()));
//	}
	
	private void assignNumberDetailBlocks(BibRef[] bibRefs) {
		
		//	run majority vote over number block semantics
		CountingSet numberDetailOrders = new CountingSet();
		for (int r = 0; r < bibRefs.length; r++) {
			if (bibRefs[r].preExistingStructure)
				continue;
			for (int b = 0; b < bibRefs[r].numberDetailBlocks.length; b++)
				numberDetailOrders.add((String) bibRefs[r].numberDetailBlocks[b].getAttribute("ndo"));
		}
		String numberDetailOrder = null;
		int numberDetailOrderScore = 0;
		if (DEBUG) System.out.println("Selecting number detail block schema:");
		for (Iterator ndoit = numberDetailOrders.iterator(); ndoit.hasNext();) {
			String ndOrder = ((String) ndoit.next());
			int ndOrderScore = (ndOrder.length() * numberDetailOrders.getCount(ndOrder));
			if (DEBUG) System.out.println(" - " + ndOrder + " (score " + ndOrderScore + " in " + numberDetailOrders.getCount(ndOrder) + " references)");
			if (ndOrderScore > numberDetailOrderScore) {
				numberDetailOrder = ndOrder;
				numberDetailOrderScore = ndOrderScore;
				if (DEBUG) System.out.println("   ==> new best match");
			}
		}
		
		//	anything to filter by?
		if (numberDetailOrder == null)
			return;
		
		//	use that for filtering
		for (int r = 0; r < bibRefs.length; r++) {
			if (bibRefs[r].preExistingStructure)
				continue;
			if (DEBUG) System.out.println(" - selecting number detail block in " + bibRefs[r].annotation.toXML());
			for (int b = 0; b < bibRefs[r].numberDetailBlocks.length; b++) {
				String ndOrder = ((String) bibRefs[r].numberDetailBlocks[b].getAttribute("ndo"));
				if (numberDetailOrder.equals(ndOrder))
					bibRefs[r].numberDetailBlock = bibRefs[r].numberDetailBlocks[b];
				else if ((bibRefs[r].numberDetailBlock == null) && (numberDetailOrder.indexOf(ndOrder) != -1))
					bibRefs[r].numberDetailBlock = bibRefs[r].numberDetailBlocks[b];
			}
			if (DEBUG) System.out.println("   ==> " + ((bibRefs[r].numberDetailBlock == null) ? "null" : bibRefs[r].numberDetailBlock.toXML()));
		}
	}
	
	private void filterBaseDetailNumbersByBlocks(BibRef bibRef) {
		if ((bibRef.numberDetailBlocks.length == 0) || (bibRef.numberDetailBlock == null)) {
			this.filterBaseDetailNumbersByDashes(bibRef);
			return;
		}
		if (DEBUG) System.out.println(" - filtering by number detail block " + bibRef.numberDetailBlock.toXML());
		
		//	filter out any other part designators and paginations if we have a distinctive block, as well as years if we have alternatives
		boolean[] numberDetailBlockFilter = createTokenFilter(bibRef.annotation, bibRef.numberDetailBlocks);
		if (bibRef.numberDetailBlock.hasAttribute("year"))
			bibRef.years = filterNonContained(bibRef.years, numberDetailBlockFilter, false);
		else bibRef.years = filterContained(bibRef.years, numberDetailBlockFilter, false);
		if (DEBUG) System.out.println("   - years filtered to: " + Arrays.toString(bibRef.years));
		bibRef.pageNumbers = filterNonContained(bibRef.pageNumbers, numberDetailBlockFilter, true);
		if (DEBUG) System.out.println("   - page numbers filtered to: " + Arrays.toString(bibRef.pageNumbers));
		bibRef.pageRanges = filterNonContained(bibRef.pageRanges, numberDetailBlockFilter, true);
		if (DEBUG) System.out.println("   - page ranges filtered to: " + Arrays.toString(bibRef.pageRanges));
		bibRef.partDesignators = filterNonContained(bibRef.partDesignators, numberDetailBlockFilter, true);
		if (DEBUG) System.out.println("   - part designators filtered to: " + Arrays.toString(bibRef.partDesignators));
		
		//	if we have a pagination, we can filter multiple page ranges if necessary
		if (bibRef.numberDetailBlock.hasAttribute("pagination") && (bibRef.pageRanges.length > 1)) {
			TokenSequence paginationTokens = Gamta.newTokenSequence(((String) bibRef.numberDetailBlock.getAttribute("pagination")), bibRef.annotation.getTokenizer());
			int paginationStart = TokenSequenceUtils.indexOf(bibRef.annotation, paginationTokens, bibRef.numberDetailBlock.getStartIndex());
			int paginationEnd = (paginationStart + paginationTokens.size());
			if (paginationStart != -1) {
				ArrayList pageRanges = new ArrayList();
				for (int p = 0; p < bibRef.pageRanges.length; p++) {
					if ((paginationStart <= bibRef.pageRanges[p].getStartIndex()) && (bibRef.pageRanges[p].getEndIndex() <= paginationEnd))
						pageRanges.add(bibRef.pageRanges[p]);
				}
				if (pageRanges.size() < bibRef.pageRanges.length)
					bibRef.pageRanges = ((Annotation[]) pageRanges.toArray(new Annotation[pageRanges.size()]));
				if (DEBUG) System.out.println("   - page ranges match filtered to: " + Arrays.toString(bibRef.pageRanges));
			}
		}
		
		//	if we have a page range, we can let go of single page numbers
		if (bibRef.pageRanges.length != 0)
			bibRef.pageNumbers = new Annotation[0];
		
		//	filter page numbers by matching pagination in absence of page ranges
		else for (int b = 0; b < bibRef.numberDetailBlocks.length; b++) {
			if (!bibRef.numberDetailBlocks[b].hasAttribute("pagination"))
				continue;
			String pagination = ((String) bibRef.numberDetailBlocks[b].getAttribute("pagination")).replaceAll("\\s+", "");
			if (pagination.length() < 3)
				continue; // this one would be unsafe to filter by
			ArrayList pageNumbers = new ArrayList();
			for (int p = 0; p < bibRef.pageNumbers.length; p++) {
				if (pagination.equals(bibRef.pageNumbers[p].getValue().replaceAll("\\s+", "")))
					pageNumbers.add(bibRef.pageNumbers[p]);
			}
			if (pageNumbers.size() < bibRef.pageNumbers.length)
				bibRef.pageNumbers = ((Annotation[]) pageNumbers.toArray(new Annotation[pageNumbers.size()]));
		}
		if (DEBUG) System.out.println("   - page numbers match filtered to: " + Arrays.toString(bibRef.pageNumbers));
		
		//	if we have a volume number, we can filter part designators
		if (bibRef.numberDetailBlock.hasAttribute("part")) {
			TokenSequence partTokens = Gamta.newTokenSequence(((String) bibRef.numberDetailBlock.getAttribute("part")), bibRef.annotation.getTokenizer());
			int partStart = TokenSequenceUtils.indexOf(bibRef.annotation, partTokens, bibRef.numberDetailBlock.getStartIndex());
			int partEnd = (partStart + partTokens.size());
			if (partStart != -1) {
				ArrayList partDesignators = new ArrayList();
				for (int p = 0; p < bibRef.partDesignators.length; p++) {
					if ((partStart <= bibRef.partDesignators[p].getStartIndex()) && (bibRef.partDesignators[p].getEndIndex() <= partEnd))
						partDesignators.add(bibRef.partDesignators[p]);
				}
				if (partDesignators.size() < bibRef.partDesignators.length)
					bibRef.partDesignators = ((Annotation[]) partDesignators.toArray(new Annotation[partDesignators.size()]));
				if (DEBUG) System.out.println("   - part designators match filtered to: " + Arrays.toString(bibRef.partDesignators));
			}
		}
	}
	
	private void filterBaseDetailNumbersByDashes(BibRef bibRef) {
		if (bibRef.partDesignators.length == 0)
			return;
		if (DEBUG) System.out.println(" - filtering part designators by dashes");
		
		//	collect part designators not preceded or followed by dash
		ArrayList partDesignators = new ArrayList();
		for (int p = 0; p < bibRef.partDesignators.length; p++) {
			if (DEBUG) System.out.println("   - checking possible part designator: " + bibRef.partDesignators[p].getValue());
			
			//	this one is part of some range, do not mark separately
			if ("-".equals(bibRef.annotation.valueAt(bibRef.partDesignators[p].getStartIndex() - 1))) {
				if (DEBUG) System.out.println("     --> after dash, filtered");
				continue;
			}
			else if ((bibRef.partDesignators[p].getEndIndex() < bibRef.annotation.size()) && "-".equals(bibRef.annotation.valueAt(bibRef.partDesignators[p].getEndIndex()))) {
				if (DEBUG) System.out.println("     --> before dash, filtered");
				continue;
			}
			
			//	hold on to this one
			if (DEBUG) System.out.println("     ==> retained");
			partDesignators.add(bibRef.partDesignators[p]);
		}
		
		//	place whatever we have
		bibRef.partDesignators = ((Annotation[]) partDesignators.toArray(new Annotation[partDesignators.size()]));
	}
	
	private void filterBaseDetailNumbersByPageRanges(BibRef bibRef) {
		if ((bibRef.pageRanges == null) || (bibRef.pageRanges.length == 0))
			return;
		if (DEBUG) System.out.println(" - filtering by page ranges " + Arrays.toString(bibRef.pageRanges));
		
		//	sort out years, page numbers, and part designators located inside page ranges
		boolean[] pageRangeFilter = createTokenFilter(bibRef.annotation, bibRef.pageRanges);
		bibRef.years = filterContained(bibRef.years, pageRangeFilter, false);
		if (DEBUG) System.out.println(" - years range filtered to: " + Arrays.toString(bibRef.years));
		bibRef.pageNumbers = filterContained(bibRef.pageNumbers, pageRangeFilter, true);
		if (DEBUG) System.out.println(" - page numbers range filtered to: " + Arrays.toString(bibRef.pageNumbers));
		bibRef.partDesignators = filterContained(bibRef.partDesignators, pageRangeFilter, true);
		if (DEBUG) System.out.println(" - part designators range filtered to: " + Arrays.toString(bibRef.partDesignators));
	}
	
	private void filterBaseDetailNumbersByPosition(BibRef bibRef) {
		if (bibRef.numberDetailBlock != null)
			return;
		boolean[] titleFilter = createTokenFilter(bibRef.annotation, null);
		if (bibRef.title != null)
			augmentFilteredTokens(titleFilter, bibRef.title, null);
		if (bibRef.volumeTitle != null)
			augmentFilteredTokens(titleFilter, bibRef.volumeTitle, null);
		if ((bibRef.volumeDesignator != null) && (countFilteredTokens(bibRef.volumeDesignator, titleFilter) != 0))
			bibRef.volumeDesignator = null;
		if ((bibRef.issueDesignator != null) && (countFilteredTokens(bibRef.issueDesignator, titleFilter) != 0))
			bibRef.issueDesignator = null;
		if ((bibRef.numberDesignator != null) && (countFilteredTokens(bibRef.numberDesignator, titleFilter) != 0))
			bibRef.numberDesignator = null;
		if ((bibRef.pagination != null) && (countFilteredTokens(bibRef.pagination, titleFilter) != 0))
			bibRef.pagination = null;
	}
	
	private void classifyPartDesignators(BibRef bibRef, boolean assortPartDesignators) {
		
		//	nothing to classify
		if ((bibRef.partDesignators == null) || (bibRef.partDesignators.length == 0))
			return;
		
		//	get hints
		Annotation[] partDesignatorHints = Gamta.extractAllContained(bibRef.annotation, this.partDesignatorHints, false);
		for (int h = 0; h < partDesignatorHints.length; h++) {
			String partDesignatorHint = TokenSequenceUtils.concatTokens(partDesignatorHints[h], true, true);
			String partDesignatorType = null;
			if (this.volumeDesignatorHints.containsIgnoreCase(partDesignatorHint))
				partDesignatorType = VOLUME_DESIGNATOR_TYPE;
			else if (this.issueDesignatorHints.containsIgnoreCase(partDesignatorHint))
				partDesignatorType = ISSUE_DESIGNATOR_TYPE;
			else if (this.numberDesignatorHints.containsIgnoreCase(partDesignatorHint))
				partDesignatorType = NUMBER_DESIGNATOR_TYPE;
			else if (this.fascicleDesignatorHints.containsIgnoreCase(partDesignatorHint))
				partDesignatorType = FASCICLE_DESIGNATOR_TYPE;
			else if (this.seriesDesignatorHints.containsIgnoreCase(partDesignatorHint))
				partDesignatorType = SERIES_DESIGNATOR_TYPE;
			if (partDesignatorType != null) {
				partDesignatorHints[h].setAttribute(TYPE_ATTRIBUTE, partDesignatorType);
				bibRef.partDesignatorHints.put(new Integer(partDesignatorHints[h].getEndIndex()), partDesignatorHints[h]);
			}
		}
		
		//	exploit hints
		for (int p = 0; p < bibRef.partDesignators.length; p++) {
			Annotation partDesignatorHint = ((Annotation) bibRef.partDesignatorHints.get(new Integer(bibRef.partDesignators[p].getStartIndex())));
			if (partDesignatorHint != null) {
//				if (SERIES_DESIGNATOR_TYPE.equals(partDesignatorHint.getAttribute(TYPE_ATTRIBUTE))) {
//					if (bibRef.partDesignators[p].length() < 2)
//						bibRef.partDesignators[p].setAttribute(TYPE_ATTRIBUTE, partDesignatorHint.getAttribute(TYPE_ATTRIBUTE));
//				}
//				else bibRef.partDesignators[p].setAttribute(TYPE_ATTRIBUTE, partDesignatorHint.getAttribute(TYPE_ATTRIBUTE));
				bibRef.partDesignators[p].setAttribute(TYPE_ATTRIBUTE, partDesignatorHint.getAttribute(TYPE_ATTRIBUTE));
			}
			else if (bibRef.numberDetailBlock != null)
				continue; // use order inference here
			else if (bibRef.partDesignators[p].size() == 1) {
				String partDesignator = bibRef.partDesignators[p].firstValue();
				if (partDesignator.matches("[A-Z]"))
					bibRef.partDesignators[p].setAttribute(TYPE_ATTRIBUTE, SERIES_DESIGNATOR_TYPE);
				else if (partDesignator.matches("[IVXivx]+"))
					bibRef.partDesignators[p].setAttribute(TYPE_ATTRIBUTE, FASCICLE_DESIGNATOR_TYPE);
			}
		}
		
		//	collect part types already used
		HashSet usedPartDesignatorTypes = new HashSet();
		for (int p = 0; p < bibRef.partDesignators.length; p++) {
			if (bibRef.partDesignators[p].hasAttribute(TYPE_ATTRIBUTE))
				usedPartDesignatorTypes.add(bibRef.partDesignators[p].getAttribute(TYPE_ATTRIBUTE));
		}
		
		//	sort out classified part designators, check brackets for rest
		ArrayList classified = new ArrayList();
		ArrayList noBrackets = new ArrayList();
		ArrayList inBrackets = new ArrayList();
		for (int p = 0; p < bibRef.partDesignators.length; p++) {
			
			//	we're already sure about this one
			if (bibRef.partDesignators[p].hasAttribute(TYPE_ATTRIBUTE)) {
				classified.add(bibRef.partDesignators[p]);
				continue;
			}
			
			//	no room for brackets
			if ((bibRef.partDesignators[p].getStartIndex() == 0) || (bibRef.partDesignators[p].getEndIndex() == bibRef.annotation.size())) {
				noBrackets.add(bibRef.partDesignators[p]);
				continue;
			}
			
			//	inspect tokens before and after
			String before = bibRef.annotation.valueAt(bibRef.partDesignators[p].getStartIndex()-1);
			String after = bibRef.annotation.valueAt(bibRef.partDesignators[p].getEndIndex());
			if ((bibRef.numberDetailBlock != null) && ("(".equals(before) || ")".equals(after)))
				inBrackets.add(bibRef.partDesignators[p]);
			else if ((")".equals(after) || "/".equals(after)) && ("(".equals(before) || bibRef.partDesignatorHints.containsKey(new Integer(bibRef.partDesignators[p].getStartIndex()))))
				inBrackets.add(bibRef.partDesignators[p]);
			else if (")".equals(after) && ("(".equals(before) || "/".equals(before) || bibRef.partDesignatorHints.containsKey(new Integer(bibRef.partDesignators[p].getStartIndex()))))
				inBrackets.add(bibRef.partDesignators[p]);
			else noBrackets.add(bibRef.partDesignators[p]);
		}
		
		//	we have an explicit volume number, make ones in brackets issues (choose later, after journal marked
		if (usedPartDesignatorTypes.contains(VOLUME_DESIGNATOR_TYPE)) {
			for (int i = 0; i < inBrackets.size(); i++)
				((Annotation) inBrackets.get(i)).setAttribute(TYPE_ATTRIBUTE, ISSUE_DESIGNATOR_TYPE);
		}
		
		//	we have a likely volume number, make ones in brackets issues (choose later, after journal marked
		else if (noBrackets.size() != 0) {
			for (int i = 0; i < inBrackets.size(); i++)
				((Annotation) inBrackets.get(i)).setAttribute(TYPE_ATTRIBUTE, ISSUE_DESIGNATOR_TYPE);
			for (int n = 0; n < noBrackets.size(); n++)
				((Annotation) noBrackets.get(n)).setAttribute(TYPE_ATTRIBUTE, VOLUME_DESIGNATOR_TYPE);
		}
		
		//	only part designators in brackets, make them volume numbers
		else for (int i = 0; i < inBrackets.size(); i++)
			((Annotation) inBrackets.get(i)).setAttribute(TYPE_ATTRIBUTE, VOLUME_DESIGNATOR_TYPE);
		
		//	report
		if (DEBUG) {
			System.out.println("Classified part designators in " + bibRef.annotation.toXML());
			for (int p = 0; p < bibRef.partDesignators.length; p++)
				System.out.println(" - " + bibRef.partDesignators[p].toXML());
		}
		
		//	assortion waived
		if (!assortPartDesignators)
			return;
		
		//	sort part designators
		ArrayList volumeDesignators = new ArrayList();
		ArrayList issueDesignators = new ArrayList();
		ArrayList numberDesignators = new ArrayList();
		ArrayList fascicleDesignators = new ArrayList();
		ArrayList seriesDesignators = new ArrayList();
		for (int p = 0; p < bibRef.partDesignators.length; p++) {
			String partDesignatorType = ((String) bibRef.partDesignators[p].getAttribute(TYPE_ATTRIBUTE));
			if (VOLUME_DESIGNATOR_TYPE.equals(partDesignatorType))
				volumeDesignators.add(bibRef.partDesignators[p]);
			else if (ISSUE_DESIGNATOR_TYPE.equals(partDesignatorType))
				issueDesignators.add(bibRef.partDesignators[p]);
			else if (NUMBER_DESIGNATOR_TYPE.equals(partDesignatorType))
				numberDesignators.add(bibRef.partDesignators[p]);
			else if (FASCICLE_DESIGNATOR_TYPE.equals(partDesignatorType))
				fascicleDesignators.add(bibRef.partDesignators[p]);
			else if (SERIES_DESIGNATOR_TYPE.equals(partDesignatorType))
				seriesDesignators.add(bibRef.partDesignators[p]);
//			else System.out.println("Unassignable part designator: " + bibRef.partDesignators[p].toXML());
		}
		bibRef.volumeDesignators = ((Annotation[]) volumeDesignators.toArray(new Annotation[volumeDesignators.size()]));
		bibRef.issueDesignators = ((Annotation[]) issueDesignators.toArray(new Annotation[issueDesignators.size()]));
		bibRef.numberDesignators = ((Annotation[]) numberDesignators.toArray(new Annotation[numberDesignators.size()]));
		bibRef.fascicleDesignators = ((Annotation[]) fascicleDesignators.toArray(new Annotation[fascicleDesignators.size()]));
		bibRef.seriesDesignators = ((Annotation[]) seriesDesignators.toArray(new Annotation[seriesDesignators.size()]));
	}
	
	private Annotation[] getLabeledUrls(BibRef bibRef) {
		
		//	get and index date components
		AnnotationIndex urlPartIndex = new AnnotationIndex();
		urlPartIndex.addAnnotations(bibRef.urls, "url");
		urlPartIndex.addAnnotations(bibRef.dois, "url");
		
		//	tag and index 'available from' labels
		Annotation[] urlLabeles = Gamta.extractAllContained(bibRef.annotation, this.urlAvailableFromLabels, false);
		urlPartIndex.addAnnotations(urlLabeles, "label");
		
		//	tag dates TODO add other formats as they occur
		ArrayList labeledUrlList = new ArrayList();
		Annotation[] labeledUrls;
		labeledUrls = AnnotationPatternMatcher.getMatches(bibRef.annotation, urlPartIndex, "<label> ':'? <url>");
		labeledUrlList.addAll(Arrays.asList(labeledUrls));
		
		//	finally ...
		Collections.sort(labeledUrlList, AnnotationUtils.ANNOTATION_NESTING_ORDER);
		return ((Annotation[]) labeledUrlList.toArray(new Annotation[labeledUrlList.size()]));
	}
	
	void trimPunctuation(MutableAnnotation[] bibRefs, ProgressMonitor pm) {
		
		//	truncate leading and tailing punctuation from detail annotations
		for (int r = 0; r < bibRefs.length; r++) {
			pm.setProgress((r * 100) / bibRefs.length);
			this.truncatePunctuation(bibRefs[r], AUTHOR_ANNOTATION_TYPE, "", ".");
			this.truncatePunctuation(bibRefs[r], TITLE_ANNOTATION_TYPE, "(", "?!).");
			this.truncatePunctuation(bibRefs[r], YEAR_ANNOTATION_TYPE, "", "");
			if (detailOrigin) {
				this.truncatePunctuation(bibRefs[r], JOURNAL_NAME_ANNOTATION_TYPE, "", ".");
				this.truncatePunctuation(bibRefs[r], SERIES_IN_JOURNAL_ANNOTATION_TYPE, "", ".");
				this.truncatePunctuation(bibRefs[r], PUBLISHER_ANNOTATION_TYPE, "", ".");
				this.truncatePunctuation(bibRefs[r], LOCATION_ANNOTATION_TYPE, "", ".");
			}
			else this.truncatePunctuation(bibRefs[r], JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE, "", ".");
			this.truncatePunctuation(bibRefs[r], PART_DESIGNATOR_ANNOTATION_TYPE, "", "");
			this.truncatePunctuation(bibRefs[r], PAGINATION_ANNOTATION_TYPE, "", "");
			this.truncatePunctuation(bibRefs[r], EDITOR_ANNOTATION_TYPE, "", ".");
			this.truncatePunctuation(bibRefs[r], VOLUME_TITLE_ANNOTATION_TYPE, "(", "?!).");
		}
	}
	
	private void truncatePunctuation(MutableAnnotation bibRef, String detailType, String retainStart, String retainEnd) {
		Annotation[] details = bibRef.getAnnotations(detailType);
		for (int d = 0; d < details.length; d++) {
			if ((d == 0) && AUTHOR_ANNOTATION_TYPE.equals(detailType) && details[0].hasAttribute(authorListRepetitionMarkMarker))
				continue;
			this.truncatePunctuation(bibRef, details[d], retainStart, retainEnd);
		}
	}
	
	private Annotation truncatePunctuation(MutableAnnotation bibRef, Annotation detail, String retainStart, String retainEnd) {
		
		//	anything to work with?
		if (detail == null)
			return detail;
		
		//	truncate end first, as punctuation marks amass there more likely than at the start
		int end = detail.size();
		while (end > 0) {
			String eValue = detail.valueAt(end-1);
			if (eValue.length() > 1)
				break;
			if (Gamta.PUNCTUATION.indexOf(eValue) == -1)
				break;
			if (retainEnd.indexOf(eValue) != -1)
				break;
			if (Gamta.isClosingBracket(eValue)) {
				boolean gotOpening = false;
				for (int l = (end-1); l > 1; l--) // only check through second token, we want to truncate enclosing brackets
					if (Gamta.opens(detail.valueAt(l-1), eValue)) {
						gotOpening = true;
						break;
					}
				if (gotOpening)
					break;
			}
			end--;
		}
		
		//	check start
		int start = 0;
		while (start < end) {
			String sValue = detail.valueAt(start);
			if (sValue.length() > 1)
				break;
			if (Gamta.PUNCTUATION.indexOf(sValue) == -1)
				break;
			if (retainStart.indexOf(sValue) != -1)
				break;
			if (Gamta.isOpeningBracket(sValue)) {
				boolean gotClosing = false;
				for (int l = (start+1); l < (end - 1); l++) // only check through second-to-last token, we want to truncate enclosing brackets
					if (Gamta.closes(detail.valueAt(l), sValue)) {
						gotClosing = true;
						break;
					}
				if (gotClosing)
					break;
			}
			start++;
		}
		
		//	anything truncated?
		if ((start == 0) && (end == detail.size()))
			return detail;
		
		//	anything remaining?
		if (end <= start) {
			bibRef.removeAnnotation(detail);
			return null;
		}
		
		//	add truncated annotation
		Annotation newDetail;
		if (detail instanceof StandaloneAnnotation) {
			newDetail = Gamta.newAnnotation(bibRef, detail.getType(), (detail.getStartIndex() + start), (end - start));
			newDetail.copyAttributes(detail);
		}
		else {
			newDetail = bibRef.addAnnotation(detail.getType(), (detail.getStartIndex() + start), (end - start));
			newDetail.copyAttributes(detail);
			bibRef.removeAnnotation(detail);
		}
		return newDetail;
	}
	
	//	clean up duplicate details
	void removeDuplicateDetails(MutableAnnotation data) {
		for (int t = 0; t < this.relevantTypes.size(); t++)
			AnnotationFilter.removeDuplicates(data, this.relevantTypes.get(t));
		AnnotationFilter.removeDuplicates(data, EDITOR_ANNOTATION_TYPE);
		AnnotationFilter.removeDuplicates(data, VOLUME_TITLE_ANNOTATION_TYPE);
	}
	
	//	add detail attributes & learn
	void setDetailAttributes(MutableAnnotation[] bibRefs, ProgressMonitor pm) {
		Properties transferDetails = new Properties();
		for (int r = 0; r < bibRefs.length; r++) {
			pm.setProgress((r * 100) / bibRefs.length);
			if (bibRefs[r].hasAttribute(GOT_FEEDBACK_ATTRIBUTE)) {
				this.setDetailAttributes(bibRefs[r], transferDetails);
				this.learnDetails(bibRefs[r]);
			}
		}
	}
	private void setDetailAttributes(MutableAnnotation bibRef, Properties transferDetails) {
		MutableAnnotation[] details;
		for (int t = 0; t < this.relevantTypes.size(); t++) {
			String detailType = this.relevantTypes.get(t);
			details = bibRef.getMutableAnnotations(detailType);
			String detail = null;
			
			//	with repetition sign, make way for transfer
			if (AUTHOR_ANNOTATION_TYPE.equals(detailType))
				while ((details.length != 0) && details[0].hasAttribute(authorListRepetitionMarkMarker)) {
					MutableAnnotation[] nDetails = new MutableAnnotation[details.length - 1];
					System.arraycopy(details, 1, nDetails, 0, nDetails.length);
					if (detail == null) {
						detail = transferDetails.getProperty(detailType);
						details[0].setAttribute(REPEATED_AUTHORS_ATTRIBUTE, detail);
					}
					details = nDetails;
				}
			
			//	set URL attribute, removing whitespace from DOIs and URLs
			if (PUBLICATION_DOI_ANNOTATION_TYPE.equals(detailType) || PUBLICATION_URL_ANNOTATION_TYPE.equals(detailType)) {
				if (details.length != 0) {
					detail = TokenSequenceUtils.concatTokens(details[0], false, true).replaceAll("\\s+", "");
					if (PUBLICATION_DOI_ANNOTATION_TYPE.equals(detailType) && detail.toLowerCase().startsWith("doi:"))
						detail = "http://dx.doi.org/" + detail.substring("doi:".length());
				}
				detailType = CITED_PUBLICATION_URL_ATTRIBUTE;
			}
			
			//	set ISO access date
			else if (ACCESS_DATE_ANNOTATION_TYPE.equals(detailType)) {
				if (details.length != 0) {
					Annotation[] dates = DateTimeUtils.getDates(details[0]);
					detail = ((dates.length == 0) ? "invalid" : DateTimeUtils.parseTextDate(dates[0].getValue()));
				}
			}
			
			//	get and store detail string, reusing ones from previous references if not given explicitly
			else {
				
				//	concatenate authors and editors with separating ' & '
				if (AUTHOR_ANNOTATION_TYPE.equals(detailType) || EDITOR_ANNOTATION_TYPE.equals(detailType)) {
					for (int d = 0; d < details.length; d++) {
						if (detail == null)
							detail = TokenSequenceUtils.concatTokens(details[d], true, true);
						else detail += (" & " + TokenSequenceUtils.concatTokens(details[d], true, true));
					}
					
					//	get author from transfer list if omitted completely (not editors, though, as many references do not include or imply any)
					if ((detail == null) && AUTHOR_ANNOTATION_TYPE.equals(detailType))
						detail = transferDetails.getProperty(detailType);
				}
				
				//	use only first token for year
				else if (YEAR_ANNOTATION_TYPE.equals(detailType))
					detail = ((details.length == 0) ? transferDetails.getProperty(detailType) : details[0].firstValue());
				
				//	use only first value for all other elements
				else detail = ((details.length == 0) ? transferDetails.getProperty(detailType) : TokenSequenceUtils.concatTokens(details[0], true, true));
			}
			
			//	set or erase attribute, and store whatever we have for downstream use
			bibRef.setAttribute(detailType, detail);
			if ((detail != null) && this.transferableTypes.contains(detailType))
				transferDetails.setProperty(detailType, detail);
		}
	}
	
	MutableAnnotation[] getFeedback(MutableAnnotation data, MutableAnnotation[] bibRefs, boolean allowRemove, boolean allowSplit, ProgressMonitor pm) {
		
		//	find IDs of paragraphs surrounding the references
		Properties bibRefParagraphIDs = new Properties();
		MutableAnnotation[] paragraphs = data.getMutableAnnotations(PARAGRAPH_TYPE);
		int paragraphIndex = 0;
		for (int r = 0; r < bibRefs.length; r++) {
			
			//	find next possible containing paragraph
			while ((paragraphIndex < paragraphs.length) && (paragraphs[paragraphIndex].getEndIndex() <= bibRefs[r].getStartIndex()))
				paragraphIndex++;
			
			//	found containing paragraph, map IDs and add page number attribute
			if ((paragraphIndex < paragraphs.length) && AnnotationUtils.contains(paragraphs[paragraphIndex], bibRefs[r])) {
				bibRefParagraphIDs.setProperty(bibRefs[r].getAnnotationID(), paragraphs[paragraphIndex].getAnnotationID());
				bibRefs[r].setAttribute(PAGE_ID_ATTRIBUTE, paragraphs[paragraphIndex].getAttribute(PAGE_ID_ATTRIBUTE));
				bibRefs[r].setAttribute(PAGE_NUMBER_ATTRIBUTE, paragraphs[paragraphIndex].getAttribute(PAGE_NUMBER_ATTRIBUTE));
			}
		}
		
		//	prepare feedback dialogs
		BibRefParserFeedbackPanel[] brpfps = new BibRefParserFeedbackPanel[bibRefs.length];
		for (int r = 0; r < bibRefs.length; r++)
			brpfps[r] = this.getFeedbackPanel(bibRefs[r], data.getDocumentProperty(DOCUMENT_ID_ATTRIBUTE), bibRefParagraphIDs, allowRemove, allowSplit);
		
		//	can we issue all dialogs at once?
		if (FeedbackPanel.isMultiFeedbackEnabled()) {
			FeedbackPanel.getMultiFeedback(brpfps);
			
			//	process all feedback data together
			for (int d = 0; d < brpfps.length; d++) {
				brpfps[d].writeChanges(bibRefs[d]);
				bibRefs[d].setAttribute(PUBLICATION_TYPE_ATTRIBUTE, brpfps[d].getBibRefType().name);
				if (brpfps[d].noBibRef.isSelected())
					bibRefs[d].setAttribute(NO_BIB_REF_ATTRIBUTE, NO_BIB_REF_ATTRIBUTE);
				else bibRefs[d].removeAttribute(NO_BIB_REF_ATTRIBUTE);
				bibRefs[d].setAttribute(GOT_FEEDBACK_ATTRIBUTE, GOT_FEEDBACK_ATTRIBUTE);
			}
		}
		
		//	display dialogs one by one otherwise (allow cancel in the middle)
		else for (int d = 0; d < brpfps.length; d++) {
			pm.setProgress((d * 100) / bibRefs.length);
			if (d != 0)
				brpfps[d].addButton("Previous");
			brpfps[d].addButton("Cancel");
			if ((d+1) < brpfps.length) {
				brpfps[d].addButton("OK & Next");
				brpfps[d].addButton("Skip & Next");
			}
			else brpfps[d].addButton("OK");
			
			String aefpTitle = brpfps[d].getTitle();
			brpfps[d].setTitle(aefpTitle + " - (" + (d+1) + " of " + brpfps.length + ")");
			
			String f = brpfps[d].getFeedback();
			if (f == null)
				f = "Cancel";
			
			brpfps[d].setTitle(aefpTitle);
			
			//	current dialog submitted, process data
			if (f.startsWith("OK")) {
				brpfps[d].writeChanges(bibRefs[d]);
				bibRefs[d].setAttribute(TYPE_ATTRIBUTE, brpfps[d].getBibRefType().name);
				if (brpfps[d].noBibRef.isSelected())
					bibRefs[d].setAttribute(NO_BIB_REF_ATTRIBUTE, NO_BIB_REF_ATTRIBUTE);
				else bibRefs[d].removeAttribute(NO_BIB_REF_ATTRIBUTE);
				bibRefs[d].setAttribute(GOT_FEEDBACK_ATTRIBUTE, GOT_FEEDBACK_ATTRIBUTE);
			}
			
			//	skip current dialog
			else if (f.startsWith("Skip"))
				bibRefs[d].removeAttribute(GOT_FEEDBACK_ATTRIBUTE);
			
			//	back to previous dialog
			else if ("Previous".equals(f)) {
				bibRefs[d].removeAttribute(GOT_FEEDBACK_ATTRIBUTE);
				d-=2;
			}
			
			//	cancel from current dialog on
			else d = brpfps.length;
		}
		
		//	sort out references marked for removal, and split the ones marked for splitting
		ArrayList splitBibRefList = new ArrayList();
		for (int r = 0; r < bibRefs.length; r++) {
			if (!bibRefs[r].hasAttribute(GOT_FEEDBACK_ATTRIBUTE))
				continue;
			
			//	do remove if required
			if (bibRefs[r].hasAttribute(NO_BIB_REF_ATTRIBUTE)) {
				for (int t = 0; t < this.relevantTypes.size(); t++)
					AnnotationFilter.removeAnnotations(bibRefs[r], this.relevantTypes.get(t));
				AnnotationFilter.removeAnnotations(bibRefs[r], VOLUME_REFERENCE_ANNOTATION_TYPE);
				data.removeAnnotation(bibRefs[r]);
				continue;
			}
			
			//	check for splits
			Annotation[] splitMarkers = bibRefs[r].getAnnotations(NEXT_REFERENCE_ANNOTATION_TYPE);
			if (splitMarkers.length == 0)
				continue;
			
			//	get parent paragraph ID
			String paragraphId = bibRefParagraphIDs.getProperty(bibRefs[r].getAnnotationID(), "");
			
			//	cut original reference
			MutableAnnotation cutBibRef = data.addAnnotation(BIBLIOGRAPHIC_REFERENCE_TYPE, bibRefs[r].getStartIndex(), splitMarkers[0].getStartIndex());
			cutBibRef.copyAttributes(bibRefs[r]);
			bibRefParagraphIDs.setProperty(cutBibRef.getAnnotationID(), paragraphId);
			
			//	mark next reference
			for (int s = 0; s < splitMarkers.length; s++) {
				MutableAnnotation nextBibRef = data.addAnnotation(BIBLIOGRAPHIC_REFERENCE_TYPE, (bibRefs[r].getStartIndex() + splitMarkers[s].getStartIndex()), ((((s+1) == splitMarkers.length) ? bibRefs[r].size() : splitMarkers[s+1].getStartIndex()) - splitMarkers[s].getStartIndex()));
				nextBibRef.copyAttributes(bibRefs[r]);
				nextBibRef.removeAttribute(GOT_FEEDBACK_ATTRIBUTE);
				bibRefParagraphIDs.setProperty(nextBibRef.getAnnotationID(), paragraphId);
				for (int t = 0; t < this.relevantTypes.size(); t++) {
					AnnotationFilter.removeAnnotations(nextBibRef, this.relevantTypes.get(t));
					nextBibRef.removeAttribute(this.relevantTypes.get(t));
				}
				splitBibRefList.add(nextBibRef);
				System.out.println("Got split reference: " + nextBibRef.toXML());
			}
			
			//	clean up
			bibRefs[r].removeAttribute(GOT_FEEDBACK_ATTRIBUTE);
			AnnotationFilter.removeAnnotations(bibRefs[r], NEXT_REFERENCE_ANNOTATION_TYPE);
			
			//	replace original reference
			data.removeAnnotation(bibRefs[r]);
			bibRefs[r] = cutBibRef;
		}
		
		//	no splits
		if (splitBibRefList.isEmpty())
			return null;
		
		//	return split references for further processing
		else return ((MutableAnnotation[]) splitBibRefList.toArray(new MutableAnnotation[splitBibRefList.size()]));
	}
	
	private BibRefParserFeedbackPanel getFeedbackPanel(MutableAnnotation bibRef, String docId, Properties bibRefParagraphIDs, boolean allowRemove, boolean allowSplit) {
		String titleExtension = "";
		BibRefParserFeedbackPanel brpfp = new BibRefParserFeedbackPanel("Check Bibliographic Reference Details" + titleExtension);
		brpfp.setLabel("<HTML>Please make sure that all the details of this bibliographic reference are marked correctly." +
				"<BR>If multiple bibliographic references are clung together, annotate the details of the first one normally," +
				"<BR>&nbsp;&nbsp;and annotate the first token of any subsequent one as <B>nextRef</B> to initiate a split." +
				"<BR>If it is not a bibliographic reference at all, check the <B>Not a Bibliographic Reference</B> to indicate so." +
				"</HTML>");
		for (int t = 0; t < this.relevantTypes.size(); t++) {
			String type = this.relevantTypes.get(t);
			Color color = this.getAnnotationHighlight(type);
			if (color != null)
				brpfp.addDetailType(type, color);
		}
		if (allowSplit)
			brpfp.addDetailType(NEXT_REFERENCE_ANNOTATION_TYPE, this.getAnnotationHighlight(NEXT_REFERENCE_ANNOTATION_TYPE));
		brpfp.setAllowRemove(allowRemove);
		brpfp.setAnnotation(bibRef);
		
		//	add reference types and preset selection
		brpfp.setBibRefTypes((BibRefType[]) this.referenceTypes.values().toArray(new BibRefType[this.referenceTypes.size()]));
		if (bibRef.hasAttribute(PUBLICATION_TYPE_ATTRIBUTE))
			brpfp.setBibRefType(new BibRefType((String) bibRef.getAttribute(PUBLICATION_TYPE_ATTRIBUTE, "")));
		
		//	add background information
		brpfp.setProperty(FeedbackPanel.TARGET_DOCUMENT_ID_PROPERTY, docId);
		brpfp.setProperty(FeedbackPanel.TARGET_PAGE_NUMBER_PROPERTY, ((String) bibRef.getAttribute(PAGE_NUMBER_ATTRIBUTE)));
		brpfp.setProperty(FeedbackPanel.TARGET_PAGE_ID_PROPERTY, ((String) bibRef.getAttribute(PAGE_ID_ATTRIBUTE)));
		brpfp.setProperty(FeedbackPanel.TARGET_ANNOTATION_ID_PROPERTY, bibRefParagraphIDs.getProperty(bibRef.getAnnotationID(), ""));
		brpfp.setProperty(FeedbackPanel.TARGET_ANNOTATION_TYPE_PROPERTY, BIBLIOGRAPHIC_REFERENCE_TYPE);
		
		//	add target page number
		brpfp.setProperty(FeedbackPanel.TARGET_PAGES_PROPERTY, ((String) bibRef.getAttribute(PAGE_NUMBER_ATTRIBUTE)));
		brpfp.setProperty(FeedbackPanel.TARGET_PAGE_IDS_PROPERTY, ((String) bibRef.getAttribute(PAGE_ID_ATTRIBUTE)));
		
		//	finally ...
		return brpfp;
	}
	
	/**
	 * Feedback panel for correcting parsed bibliographic references. Has to be
	 * public and static due to the class visibility and loadability
	 * requirements of the remote feedback API.
	 * 
	 * @author sautter
	 */
	public static class BibRefParserFeedbackPanel extends FeedbackPanel {
		private static AnnotationEditorFeedbackPanelRenderer aefpRenderer = new AnnotationEditorFeedbackPanelRenderer();
		
		private AnnotationEditorFeedbackPanel annotationEditor = new AnnotationEditorFeedbackPanel();
		private FeedbackPanelHtmlRendererInstance annotationEditorRenderer;
		
		private JPanel functionPanel = new JPanel(new BorderLayout(), true);
		private JComboBox bibRefType = new JComboBox();
		private JCheckBox noBibRef = new JCheckBox("Not a Bibliographic Reference");
		
		public BibRefParserFeedbackPanel(String title) {
			super(title);
			
			this.bibRefType.setEditable(false);
			
			this.functionPanel.add(this.bibRefType, BorderLayout.WEST);
			this.functionPanel.add(this.noBibRef, BorderLayout.EAST);
			this.add(this.functionPanel, BorderLayout.NORTH);
			
//			this.annotationEditor.setFontSize(12);
//			this.annotationEditor.setFontName("Verdana");
			this.add(this.annotationEditor, BorderLayout.CENTER);
		}
		
		void setAnnotation(MutableAnnotation annotation) {
			this.annotationEditor.addAnnotation(annotation);
		}
		
		void setBibRefTypes(BibRefType[] types) {
			this.bibRefType.setModel(new DefaultComboBoxModel(types));
		}
		
		void setBibRefType(BibRefType type) {
			for (int t = 0; t < this.bibRefType.getItemCount(); t++)
				if (type.equals(this.bibRefType.getItemAt(t))) {
					this.bibRefType.setSelectedIndex(t);
					break;
				}
		}
		
		void setAllowRemove(boolean ar) {
			if (ar)
				this.noBibRef.setEnabled(true);
			else {
				this.noBibRef.setSelected(false);
				this.noBibRef.setEnabled(false);
			}
		}
		
		BibRefType getBibRefType() {
			return ((BibRefType) this.bibRefType.getSelectedItem());
		}
		
		void addDetailType(String detailType, Color color) {
			this.annotationEditor.addDetailType(detailType, color);
		}
		
		void writeChanges(MutableAnnotation target) {
			AnnotationEditorFeedbackPanel.writeChanges(this.annotationEditor.getTokenStatesAt(0), target);
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#getComplexity()
		 */
		public int getComplexity() {
			return (this.getDecisionComplexity() + this.getDecisionCount());
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#getDecisionComplexity()
		 */
		public int getDecisionComplexity() {
			return this.annotationEditor.getDecisionComplexity();
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#getDecisionCount()
		 */
		public int getDecisionCount() {
			return this.annotationEditor.getDecisionCount();
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#writeData(java.io.Writer)
		 */
		public void writeData(Writer out) throws IOException {
			BufferedWriter bw = ((out instanceof BufferedWriter) ? ((BufferedWriter) out) : new BufferedWriter(out));
			super.writeData(bw);
			
			//	add exclusion & reference types
			bw.write(this.noBibRef.isEnabled() ? (this.noBibRef.isSelected() ? "E" : "K") : "D");
			bw.newLine();
			bw.write(((BibRefType) this.bibRefType.getSelectedItem()).name);
			bw.newLine();
			for (int t = 0; t < this.bibRefType.getItemCount(); t++) {
				bw.write(((BibRefType) this.bibRefType.getItemAt(t)).toDataString());
				bw.newLine();
			}
			bw.newLine();
			
			//	write content
			this.annotationEditor.writeData(bw);
			
			//	send data
			bw.flush();
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#initFields(java.io.Reader)
		 */
		public void initFields(Reader in) throws IOException {
			BufferedReader br = ((in instanceof BufferedReader) ? ((BufferedReader) in) : new BufferedReader(in));
			super.initFields(br);
			
			//	read exclusion & selected bibRefType
			String excludeState = br.readLine();
			if ("D".equals(excludeState)) {
				this.noBibRef.setSelected(false);
				this.noBibRef.setEnabled(false);
			}
			else {
				this.noBibRef.setEnabled(true);
				this.noBibRef.setSelected("E".equals(excludeState));
			}
			String selectedType = br.readLine();
			
			//	read bibRefType list
			TreeSet types = new TreeSet();
			for (String typeData; ((typeData = br.readLine()) != null) && (typeData.length() != 0);) {
				BibRefType type = BibRefType.parseDataString(typeData);
				if (type != null)
					types.add(type);
			}
			this.setBibRefTypes((BibRefType[]) types.toArray(new BibRefType[types.size()]));
			this.setBibRefType(new BibRefType(selectedType));
			
			//	read content
			this.annotationEditor.initFields(br);
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#getFieldStates()
		 */
		public Properties getFieldStates() {
			Properties fs = this.annotationEditor.getFieldStates();
			if (fs == null)
				return null;
			fs.setProperty(("bibRefType" + 0), ((BibRefType) this.bibRefType.getSelectedItem()).name);
			fs.setProperty(("noBibRef" + 0), (this.noBibRef.isSelected() ? "E" : "K"));
			return fs;
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#setFieldStates(java.util.Properties)
		 */
		public void setFieldStates(Properties states) {
			this.annotationEditor.setFieldStates(states);
			String type = states.getProperty("bibRefType" + 0);
			if (type != null)
				this.setBibRefType(new BibRefType(type));
			this.noBibRef.setSelected("E".equals(states.getProperty(("noBibRef" + 0), "K")));
		}
		
		private final FeedbackPanelHtmlRendererInstance getRendererInstance() {
			if (this.annotationEditorRenderer == null)
				this.annotationEditorRenderer = aefpRenderer.getRendererInstance(this.annotationEditor);
			return this.annotationEditorRenderer;
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#writeJavaScriptInitFunctionBody(java.io.Writer)
		 */
		public void writeJavaScriptInitFunctionBody(Writer out) throws IOException {
			this.getRendererInstance().writeJavaScriptInitFunctionBody(out);
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#writeJavaScript(java.io.Writer)
		 */
		public void writeJavaScript(Writer out) throws IOException {
			this.getRendererInstance().writeJavaScript(out);
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#writeCssStyles(java.io.Writer)
		 */
		public void writeCssStyles(Writer out) throws IOException {
			this.getRendererInstance().writeCssStyles(out);
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#writePanelBody(java.io.Writer)
		 */
		public void writePanelBody(Writer out) throws IOException {
			BufferedLineWriter bw = ((out instanceof BufferedLineWriter) ? ((BufferedLineWriter) out) : new BufferedLineWriter(out));
			
			bw.writeLine("<table class=\"part\" id=\"part" + 0 + "\">");
			bw.writeLine("<tr>");
			
			bw.writeLine("<td>");
			bw.writeLine("Reference Type:");
			bw.writeLine("<select name=\"bibRefType" + 0 + "\">");
			for (int c = 0; c < this.bibRefType.getItemCount(); c++) {
				BibRefType type = ((BibRefType)  this.bibRefType.getItemAt(c));
				bw.writeLine("<option value=\"" + type.name + "\"" + ((c == this.bibRefType.getSelectedIndex()) ? " selected" : "") + ">" + type.label + "</option>");
			}
			bw.writeLine("</select>");
			bw.writeLine("</td>");
			
			bw.writeLine("<td>");
			bw.writeLine("</td>");
			
			bw.writeLine("<td>");
			if (this.noBibRef.isEnabled()) {
				bw.writeLine("Not a Bibliographic Reference");
				bw.writeLine("<input name=\"noBibRef" + 0 + "\" type=\"checkbox\" value=\"E\"" + (this.noBibRef.isSelected() ? " checked" : "") + ">");
			}
			bw.writeLine("</td>");
			
			bw.writeLine("</tr>");
			bw.writeLine("</table>");
			
			this.getRendererInstance().writePanelBody(bw);
			
			if (bw != out)
				bw.flush();
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#readResponse(java.util.Properties)
		 */
		public void readResponse(Properties response) {
			this.getRendererInstance().readResponse(response);
			String type = response.getProperty("bibRefType" + 0);
			if (type != null)
				this.setBibRefType(new BibRefType(type));
			this.noBibRef.setSelected("E".equals(response.getProperty(("noBibRef" + 0), "K")));
		}
	}
	
	/**
	 * 
	 * @param adp
	 * @return
	 */
	public static RefParse getInstance(AnalyzerDataProvider adp) {
		RefParse rp = ((RefParse) instances.get(adp.getAbsolutePath()));
		if (rp == null) {
			rp = new RefParse() {};
			rp.setDataProvider(adp);
			instances.put(adp.getAbsolutePath(), rp);
		}
		return rp;
	}
	private static HashMap instances = new HashMap(3);
}