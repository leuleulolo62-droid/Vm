-- ===== Key System (must pass before the script runs) =====
local function __y2k_keygate()
-- ============================================================================
--  Y2k key provider  (drop-in replacement for the Junkie SDK)
--  Talks to YOUR Cloudflare Worker + KV key server (server-side hashing, HWID
--  auto-bind, expiry). CONFIGURE the two URLs below. Server: server-example/.
-- ============================================================================
local Junkie = {}
do
	local KEY_API  = "https://y2k-keys.y2kscript.workers.dev"  -- your deployed Worker (LIVE)
	local KEY_LINK = "https://work.ink/2Dgt/ks-int12887-kq76mlra7lo" -- work.ink key link

	local HttpService = game:GetService("HttpService")
	local function enc(s) local ok, r = pcall(function() return HttpService:UrlEncode(s) end) return ok and r or s end
	local function httpGet(u)
		for _, f in ipairs({
			function() return game:HttpGetAsync(u) end,
			function() return game:HttpGet(u) end,
			function() return request and request({ Url = u, Method = "GET" }).Body end,
		}) do
			local ok, b = pcall(f); if ok and type(b) == "string" then return b end
		end
		return nil
	end
	local function hwid()
		local id
		pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
		if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
		return tostring(id or "unknown")
	end

	function Junkie.get_key_link() return KEY_LINK end
	function Junkie.check_key(key)
		if not key or key == "" then return { valid = false, message = "No key entered" } end
		local hw = hwid()
		local url = KEY_API .. "/check?key=" .. enc(key) .. "&hwid=" .. enc(hw) .. "&t=" .. tostring(os.time())
		local body = httpGet(url)
		if not body then return { valid = false, message = "Key server unreachable" } end
		local b = string.lower(body)
		if string.find(b, "ok", 1, true) then
			getgenv().HWID = hw
			return { valid = true, message = "KEY_VALID", hwid = hw }
		elseif string.find(b, "expired", 1, true) then
			return { valid = false, message = "Key expired" }
		elseif string.find(b, "hwid", 1, true) then
			return { valid = false, message = "Key locked to another device" }
		else
			return { valid = false, message = "Invalid key" }
		end
	end
end


local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local RunService = game:GetService("RunService")
local Players = game:GetService("Players")
local Lighting = game:GetService("Lighting")
local HttpService = game:GetService("HttpService")

local Icons = {
	Shield = "rbxassetid://105619007041452",
	Loading = "rbxassetid://116535712789945",
	Lock = "rbxassetid://114355063515473",
	Key = "rbxassetid://93569468678423",
	Check = "rbxassetid://119783053916823",
	CheckCircle = "rbxassetid://10709790644",
	XCircle = "rbxassetid://10747384394",
	Warning = "rbxassetid://130226573962640",
	Globe = "rbxassetid://10734950309",
	Info = "rbxassetid://94529541997278",
	ExternalLink = "rbxassetid://71038734318580",
	Copy = "rbxassetid://107485544510830",
	Spinner = "rbxassetid://10709767827",
	Database = "rbxassetid://114209748010261",
	Sparkles = "rbxassetid://10709767827",
	ErrorFolder = "rbxassetid://113312905787220",
	Candy = "rbxassetid://10709767827",
	JunkieNewIcon = "rbxassetid://75038032192167"
}

local function hasFileSystemSupport()
    local hasWritefile = pcall(function() return type(writefile) == "function" end)
    local hasReadfile = pcall(function() return type(readfile) == "function" end)
    local hasIsfile = pcall(function() return type(isfile) == "function" end)
    return hasWritefile and hasReadfile and hasIsfile
end

local fileSystemSupported = hasFileSystemSupport()

local function saveVerifiedKey(key)
    if not fileSystemSupported then return false end
    local ok = pcall(function()
        writefile("verified_key.txt", key)
    end)
    return ok
end

local function loadVerifiedKey()
    if not fileSystemSupported then 
        return nil 
    end
    
    local ok, content = pcall(function()
        return readfile("verified_key.txt")
    end)
    
    if not ok or not content then 
        return nil 
    end
    return content
end

local function clearSavedKey()
    if not fileSystemSupported then return false end
    local ok = pcall(function() delfile("verified_key.txt") end)
    return ok
end

local Configuration = {
	ScreenGuiName = "JunkieKeySystem",
	Window = {Size = UDim2.new(0, 333, 0, 500)},
	Colors = {
		Bg = Color3.fromRGB(12, 12, 12),
		Primary = Color3.fromRGB(59, 130, 246),
		PrimaryDark = Color3.fromRGB(37, 99, 235),
		StatusIdle = Color3.fromRGB(249, 115, 22),
		StatusSuccess = Color3.fromRGB(16, 185, 129),
		StatusError = Color3.fromRGB(239, 68, 68),
		StatusVerifying = Color3.fromRGB(59, 130, 246),
		StatusWarning = Color3.fromRGB(254, 188, 46),
		TextMain = Color3.fromRGB(255, 255, 255),
		TextSec = Color3.fromRGB(161, 161, 170),
		TextMuted = Color3.fromRGB(113, 113, 122),
		Border = Color3.fromRGB(255, 255, 255),
		TrafficRed = Color3.fromRGB(255, 95, 87),
		TrafficYellow = Color3.fromRGB(254, 188, 46),
		TrafficGreen = Color3.fromRGB(40, 200, 64),
		Success = Color3.fromRGB(50, 205, 110),
		Error = Color3.fromRGB(245, 70, 90),
		Warning = Color3.fromRGB(255, 200, 50)
	},
	BorderTransparency = 0.15,
	Animations = {
		VeryFast = 0.1,
		Fast = 0.2,
		Medium = 0.4,
		Slow = 0.5,
		VerySlow = 0.6,
		Bounce = 0.6
	},
	Fonts = {
		Title = 24,
		Subtitle = 12,
		Button = 14,
		Input = 16,
		Body = 13,
		Small = 11,
		Tiny = 12
	}
}

local Utils = {}

Utils.Tween = function(obj, props, time, style, dir)
	local t =
		TweenService:Create(
		obj,
		TweenInfo.new(time or 0.3, style or Enum.EasingStyle.Quint, dir or Enum.EasingDirection.Out),
		props
	)
	t:Play()
	return t
end

Utils.CreateCorner = function(parent, radius)
	local corner = Instance.new("UICorner")
	corner.CornerRadius = UDim.new(0, radius or Configuration.CornerRadius)
	corner.Parent = parent
	return corner
end

Utils.Round = function(obj, radius)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, radius or 12)
	c.Parent = obj
	return c
end

Utils.TweenBack = function(instance, properties, duration)
	return Utils.Tween(instance, properties, duration, Enum.EasingStyle.Back, Enum.EasingDirection.Out)
end

Utils.CreateStroke = function(parent, color, thickness, transparency)
	local stroke = Instance.new("UIStroke")
	stroke.Color = color or Configuration.Colors.Border
	stroke.Thickness = thickness or 1
	stroke.Transparency = transparency or 0.77
	stroke.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	stroke.Parent = parent
	return stroke
end

Utils.Stroke = function(obj, color, thick, trans)
	local s = Instance.new("UIStroke")
	s.Color = color or Color3.new(1, 1, 1)
	s.Thickness = thick or 1
	s.Transparency = trans or 0.9
	s.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	s.Parent = obj
	return s
end

Utils.CreateGradient = function(parent, color1, color2, rotation)
	local gradient = Instance.new("UIGradient")
	gradient.Color =
		ColorSequence.new(
		{
			ColorSequenceKeypoint.new(0, color1),
			ColorSequenceKeypoint.new(1, color2)
		}
	)
	gradient.Rotation = rotation or 300
	gradient.Parent = parent
	return gradient
end

local function SetBlur(enabled)
	local blur = Lighting:FindFirstChild("JunkieBlur")
	if enabled then
		if not blur then
			blur = Instance.new("BlurEffect")
			blur.Name = "JunkieBlur"
			blur.Size = 0
			blur.Parent = Lighting
		end
		Utils.Tween(blur, {Size = 24}, Configuration.Animations.Bounce)
	elseif blur then
		Utils.Tween(blur, {Size = 0}, Configuration.Animations.Medium)
		task.delay(
			0.4,
			function()
				blur:Destroy()
			end
		)
	end
end

local ToastSystem = {ActiveToasts = {}, MaxToasts = 3, ToastSpacing = 10}

ToastSystem.Create = function(parent, message, toastType, duration, statusCode)
	local colors = {
		success = Configuration.Colors.Success,
		error = Configuration.Colors.Error,
		warning = Configuration.Colors.Warning,
		info = Configuration.Colors.Primary
	}
	local icons = {
		success = Icons.CheckCircle,
		error = Icons.ErrorFolder,
		warning = Icons.Warning,
		info = Icons.Info
	}
	local toastColor = colors[toastType] or colors.Bg
	local toastIcon = icons[toastType] or nil
	if #ToastSystem.ActiveToasts >= ToastSystem.MaxToasts then
		local oldest = table.remove(ToastSystem.ActiveToasts, 1)
		if oldest and oldest.Parent then
			oldest:Destroy()
		end
	end
	local toastHeight = 56
	local toast = Instance.new("Frame")
	toast.Name = tick()
	toast.Size = UDim2.new(0, 0, 0, toastHeight)
	toast.Position = UDim2.new(0.5, 0, 0, 20)
	toast.AnchorPoint = Vector2.new(0.5, 0)
	toast.BackgroundColor3 = Configuration.Colors.Bg
	toast.BackgroundTransparency = 0.5
	toast.BorderSizePixel = 0
	toast.ZIndex = 300
	toast.ClipsDescendants = true
	toast.Parent = parent
	Utils.Round(toast, 14)
	Utils.CreateStroke(toast, toastColor, 1, 0.1)
	Utils.CreateGradient(toast, Configuration.Colors.Bg, Configuration.Colors.Bg, 1)
	local iconBg = Instance.new("Frame")
	iconBg.Name = "IconBg"
	iconBg.Size = UDim2.new(0, 36, 0, 36)
	iconBg.Position = UDim2.new(0, 12, 0.5, 0)
	iconBg.AnchorPoint = Vector2.new(0, 0.5)
	iconBg.BackgroundColor3 = toastColor
	iconBg.BackgroundTransparency = 0.85
	iconBg.BorderSizePixel = 0
	iconBg.ZIndex = 301
	iconBg.Parent = toast
	Utils.Round(iconBg, 18)
	local icon = Instance.new("ImageLabel")
	icon.Name = "Icon"
	icon.Size = UDim2.new(0, 20, 0, 20)
	icon.Position = UDim2.new(0.5, 0, 0.5, 0)
	icon.AnchorPoint = Vector2.new(0.5, 0.5)
	icon.BackgroundTransparency = 1
	icon.Image = toastIcon
	icon.ImageColor3 = toastColor
	icon.ZIndex = 302
	icon.Parent = iconBg
	local textContainer = Instance.new("Frame")
	textContainer.Name = "TextContainer"
	textContainer.Size = UDim2.new(1, statusCode and -110 or -60, 1, 0)
	textContainer.Position = UDim2.new(0, 56, 0, 0)
	textContainer.BackgroundTransparency = 1
	textContainer.ZIndex = 301
	textContainer.Parent = toast
	local text = Instance.new("TextLabel")
	text.Name = "Message"
	text.Size = UDim2.new(1, 0, 1, 0)
	text.BackgroundTransparency = 1
	text.Text = message or ""
	text.TextColor3 = Configuration.Colors.TextMain
	text.TextSize = Configuration.Fonts.Body
	text.Font = Enum.Font.GothamMedium
	text.TextXAlignment = Enum.TextXAlignment.Left
	text.TextYAlignment = Enum.TextYAlignment.Center
	text.TextWrapped = true
	text.ZIndex = 301
	text.Parent = textContainer
	if statusCode then
		local statusBadge = Instance.new("Frame")
		statusBadge.Name = "StatusBadge"
		statusBadge.Size = UDim2.new(0, 44, 0, 28)
		statusBadge.Position = UDim2.new(1, -12, 0.5, 0)
		statusBadge.AnchorPoint = Vector2.new(1, 0.5)
		statusBadge.BackgroundColor3 = toastColor
		statusBadge.BackgroundTransparency = 0.8
		statusBadge.BorderSizePixel = 0
		statusBadge.ZIndex = 301
		statusBadge.Parent = toast
		Utils.Round(statusBadge, 8)
		Utils.CreateStroke(statusBadge, toastColor, 1, Configuration.BorderTransparency)
		local statusCodeLabel = Instance.new("TextLabel")
		statusCodeLabel.Name = "StatusCode"
		statusCodeLabel.Size = UDim2.new(1, 0, 1, 0)
		statusCodeLabel.BackgroundTransparency = 1
		statusCodeLabel.Text = tostring(statusCode)
		statusCodeLabel.TextColor3 = toastColor
		statusCodeLabel.TextSize = Configuration.Fonts.Small
		statusCodeLabel.Font = Enum.Font.GothamBold
		statusCodeLabel.ZIndex = 302
		statusCodeLabel.Parent = statusBadge
	end
	table.insert(ToastSystem.ActiveToasts, toast)
	ToastSystem.RepositionToasts()
	local targetWidth = 320
	Utils.TweenBack(toast, {Size = UDim2.new(0, targetWidth, 0, toastHeight)}, Configuration.Animations.Medium)
	task.delay(
		duration or 3.5,
		function()
			if toast.Parent then
				Utils.Tween(
					toast,
					{
						Position = UDim2.new(0.5, 0, 0, -80),
						BackgroundTransparency = 1
					},
					Configuration.Animations.Medium
				)
				for i, t in ipairs(ToastSystem.ActiveToasts) do
					if t == toast then
						table.remove(ToastSystem.ActiveToasts, i)
						break
					end
				end
				task.wait(Configuration.Animations.Medium)
				toast:Destroy()
				ToastSystem.RepositionToasts()
			end
		end
	)
	return toast
end

ToastSystem.RepositionToasts = function()
	for i, toast in ipairs(ToastSystem.ActiveToasts) do
		local targetY = 20 + ((i - 1) * (60 + ToastSystem.ToastSpacing))
		Utils.Tween(toast, {Position = UDim2.new(0.5, 0, 0, targetY)}, Configuration.Animations.Medium)
	end
end

local function Build()
	local parent = game:GetService("CoreGui")
	local old = parent:FindFirstChild(Configuration.ScreenGuiName)
	if old then
		old:Destroy()
	end
	local screen = Instance.new("ScreenGui")
	screen.Name = Configuration.ScreenGuiName
	screen.ResetOnSpawn = false
	screen.Parent = parent

	-- Discord banner (top of screen, transparent, blinking + glow)
	local discordBanner = Instance.new("TextLabel")
	discordBanner.Name = "DiscordBanner"
	discordBanner.Size = UDim2.new(0, 400, 0, 32)
	discordBanner.Position = UDim2.new(0.5, 0, 0, 10)
	discordBanner.AnchorPoint = Vector2.new(0.5, 0)
	discordBanner.BackgroundTransparency = 1
	discordBanner.Text = "Join https://discord.gg/EFFKrfFkPQ"
	discordBanner.TextColor3 = Color3.fromRGB(88, 101, 242)
	discordBanner.TextSize = 16
	discordBanner.Font = Enum.Font.GothamBold
	discordBanner.TextTransparency = 0
	discordBanner.Parent = screen

	local bannerStroke = Instance.new("UIStroke")
	bannerStroke.Color = Color3.fromRGB(88, 101, 242)
	bannerStroke.Thickness = 2
	bannerStroke.Transparency = 0.3
	bannerStroke.Parent = discordBanner

	task.spawn(function()
		while discordBanner and discordBanner.Parent do
			Utils.Tween(discordBanner, {TextTransparency = 0.4}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.7}, 0.6)
			task.wait(0.6)
			Utils.Tween(discordBanner, {TextTransparency = 0}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.3}, 0.6)
			task.wait(0.6)
		end
	end)

	local overlay = Instance.new("Frame")
	overlay.Size = UDim2.fromScale(1, 1)
	overlay.BackgroundColor3 = Color3.new(0, 0, 0)
	overlay.BackgroundTransparency = 1
	overlay.Parent = screen
	Utils.Tween(overlay, {BackgroundTransparency = 1}, 1)
	SetBlur(true)
	local main = Instance.new("Frame")
	main.Size = Configuration.Window.Size
	main.Position = UDim2.new(0.5, 0, 0.5, 60)
	main.AnchorPoint = Vector2.new(0.5, 0.5)
	main.BackgroundColor3 = Configuration.Colors.Bg
	main.BackgroundTransparency = 0.2
	main.ClipsDescendants = true
	main.Parent = screen
	Utils.Round(main, 24)
	Utils.Stroke(main, Color3.new(1, 1, 1), 1, 0.92)
	local glass = Instance.new("Frame")
	glass.Size = UDim2.fromScale(1, 1)
	glass.BackgroundColor3 = Color3.new(1, 1, 1)
	glass.BackgroundTransparency = 0.985
	glass.ZIndex = 0
	glass.Parent = main
	Utils.Round(glass, 24)
	local bar = Instance.new("Frame")
	bar.Size = UDim2.new(1, 0, 0, 54)
	bar.BackgroundTransparency = 1
	bar.Parent = main
	local dots = Instance.new("Frame")
	dots.Size = UDim2.new(0, 54, 0, 12)
	dots.Position = UDim2.new(0, 20, 0.5, 0)
	dots.AnchorPoint = Vector2.new(0, 0.5)
	dots.BackgroundTransparency = 1
	dots.Parent = bar
	local dColors = {
		Configuration.Colors.TrafficRed,
		Configuration.Colors.TrafficYellow,
		Configuration.Colors.TrafficGreen
	}
	for i, c in ipairs(dColors) do
		local d = Instance.new("Frame")
		d.Size = UDim2.fromOffset(12, 12)
		d.Position = UDim2.fromOffset((i - 1) * 18, 0)
		d.BackgroundColor3 = c
		d.BorderSizePixel = 0
		d.Parent = dots
		Utils.Round(d, 6)
	end
	local titleText = Instance.new("TextLabel")
	titleText.Size = UDim2.new(1, 0, 1, 0)
	titleText.Text = "JUNKIE"
	titleText.TextColor3 = Color3.new(1, 1, 1)
	titleText.TextTransparency = 0.7
	titleText.TextSize = 10
	titleText.Font = Enum.Font.GothamBold
	titleText.BackgroundTransparency = 1
	titleText.Parent = bar
	local content = Instance.new("ScrollingFrame")
	content.Size = UDim2.new(1, 0, 1, -54)
	content.Position = UDim2.new(0, 0, 0, 54)
	content.BackgroundTransparency = 1
	content.ScrollBarThickness = 0
	content.CanvasSize = UDim2.new(0, 0, 0, 440)
	content.Parent = main
	local list = Instance.new("UIListLayout")
	list.Padding = UDim.new(0, 24)
	list.HorizontalAlignment = Enum.HorizontalAlignment.Center
	list.Parent = content
	local pad = Instance.new("UIPadding")
	pad.PaddingTop = UDim.new(0, 5)
	pad.Parent = content
	local logoContainer = Instance.new("Frame")
	logoContainer.Size = UDim2.fromOffset(80, 80)
	logoContainer.BackgroundColor3 = Configuration.Colors.Primary
	logoContainer.Parent = content
	Utils.Round(logoContainer, 20)
	local grad = Instance.new("UIGradient")
	grad.Color = ColorSequence.new(Configuration.Colors.Primary, Configuration.Colors.PrimaryDark)
	grad.Rotation = 45
	grad.Parent = logoContainer
	local sIcon = Instance.new("ImageLabel")
	sIcon.Size = UDim2.fromScale(1, 1)
	sIcon.Position = UDim2.fromScale(0.5, 0.5)
	sIcon.AnchorPoint = Vector2.new(0.5, 0.5)
	sIcon.Image = Icons.JunkieNewIcon
	sIcon.ScaleType = Enum.ScaleType.Fit
	sIcon.BackgroundTransparency = 1
	sIcon.Parent = logoContainer
	local titleArea = Instance.new("Frame")
	titleArea.Size = UDim2.new(1, 0, 0, 44)
	titleArea.BackgroundTransparency = 1
	titleArea.Parent = content
	local mainTitle = Instance.new("TextLabel")
	mainTitle.Size = UDim2.new(1, 0, 0, 26)
	mainTitle.Text = "Junkie"
	mainTitle.TextColor3 = Color3.new(1, 1, 1)
	mainTitle.TextSize = 26
	mainTitle.Font = Enum.Font.GothamBold
	mainTitle.BackgroundTransparency = 1
	mainTitle.Parent = titleArea
	local subTitle = Instance.new("TextLabel")
	subTitle.Size = UDim2.new(1, 0, 0, 16)
	subTitle.Position = UDim2.fromOffset(0, 28)
	subTitle.Text = "junkie-development.de"
	subTitle.TextColor3 = Configuration.Colors.TextSec
	subTitle.TextSize = 13
	subTitle.Font = Enum.Font.Gotham
	subTitle.BackgroundTransparency = 1
	subTitle.Parent = titleArea
	local statusCard = Instance.new("Frame")
	statusCard.Size = UDim2.new(0, 280, 0, 68)
	statusCard.BackgroundColor3 = Color3.new(1, 1, 1)
	statusCard.BackgroundTransparency = 0.96
	statusCard.Parent = content
	Utils.Round(statusCard, 16)
	local sStroke = Utils.Stroke(statusCard, Color3.new(1, 1, 1), 1, 0.95)
	local sIconBg = Instance.new("Frame")
	sIconBg.Size = UDim2.fromOffset(42, 42)
	sIconBg.Position = UDim2.new(0, 14, 0.5, 0)
	sIconBg.AnchorPoint = Vector2.new(0, 0.5)
	sIconBg.BackgroundColor3 = Configuration.Colors.StatusIdle
	sIconBg.BackgroundTransparency = 0.9
	sIconBg.Parent = statusCard
	Utils.Round(sIconBg, 21)
	local sImg = Instance.new("ImageLabel")
	sImg.Size = UDim2.fromScale(0.5, 0.5)
	sImg.Position = UDim2.fromScale(0.5, 0.5)
	sImg.AnchorPoint = Vector2.new(0.5, 0.5)
	sImg.Image = Icons.Lock
	sImg.ImageColor3 = Configuration.Colors.StatusIdle
	sImg.BackgroundTransparency = 1
	sImg.Parent = sIconBg
	local sLabel = Instance.new("TextLabel")
	sLabel.Size = UDim2.new(1, -70, 0, 14)
	sLabel.Position = UDim2.fromOffset(70, 16)
	sLabel.Text = "CURRENT STATUS"
	sLabel.TextColor3 = Configuration.Colors.TextMuted
	sLabel.TextSize = 10
	sLabel.Font = Enum.Font.GothamBold
	sLabel.TextXAlignment = Enum.TextXAlignment.Left
	sLabel.BackgroundTransparency = 1
	sLabel.Parent = statusCard
	local sValue = Instance.new("TextLabel")
	sValue.Size = UDim2.new(1, -70, 0, 20)
	sValue.Position = UDim2.fromOffset(70, 32)
	sValue.Text = "No key detected"
	sValue.TextColor3 = Configuration.Colors.StatusIdle
	sValue.TextSize = 15
	sValue.Font = Enum.Font.GothamMedium
	sValue.TextXAlignment = Enum.TextXAlignment.Left
	sValue.BackgroundTransparency = 1
	sValue.Parent = statusCard
	local inputFrame = Instance.new("Frame")
	inputFrame.Size = UDim2.new(0, 280, 0, 52)
	inputFrame.BackgroundColor3 = Color3.new(1, 1, 1)
	inputFrame.BackgroundTransparency = 0.975
	inputFrame.Parent = content
	Utils.Round(inputFrame, 14)
	local iStroke = Utils.Stroke(inputFrame, Color3.new(1, 1, 1), 1, 0.95)
	local kIcon = Instance.new("ImageLabel")
	kIcon.Size = UDim2.fromOffset(18, 18)
	kIcon.Position = UDim2.new(0, 14, 0.5, 0)
	kIcon.AnchorPoint = Vector2.new(0, 0.5)
	kIcon.Image = Icons.Key
	kIcon.ImageColor3 = Configuration.Colors.TextMuted
	kIcon.BackgroundTransparency = 1
	kIcon.Parent = inputFrame
	local box = Instance.new("TextBox")
	box.Size = UDim2.new(1, -85, 1, 0)
	box.Position = UDim2.fromOffset(45, 0)
	box.Text = ""
	box.PlaceholderText = "Enter your key..."
	box.TextColor3 = Color3.new(1, 1, 1)
	box.TextSize = 14
	box.Font = Enum.Font.Gotham
	box.BackgroundTransparency = 1
	box.TextXAlignment = Enum.TextXAlignment.Left
	box.Parent = inputFrame
	local paste = Instance.new("ImageButton")
	paste.Size = UDim2.fromOffset(18, 18)
	paste.Position = UDim2.new(1, -14, 0.5, 0)
	paste.AnchorPoint = Vector2.new(1, 0.5)
	paste.Image = Icons.Copy
	paste.ImageColor3 = Configuration.Colors.TextMuted
	paste.BackgroundTransparency = 1
	paste.Parent = inputFrame
	local btnRow = Instance.new("Frame")
	btnRow.Size = UDim2.new(0, 280, 0, 50)
	btnRow.BackgroundTransparency = 1
	btnRow.Parent = content
	local redeem = Instance.new("TextButton")
	redeem.Size = UDim2.new(0.5, -8, 1, 0)
	redeem.BackgroundColor3 = Configuration.Colors.Primary
	redeem.Text = "Redeem"
	redeem.TextColor3 = Color3.new(1, 1, 1)
	redeem.Font = Enum.Font.GothamBold
	redeem.TextSize = 14
	redeem.AutoButtonColor = false
	redeem.Parent = btnRow
	Utils.Round(redeem, 14)
	local getKey = Instance.new("TextButton")
	getKey.Size = UDim2.new(0.5, -8, 1, 0)
	getKey.Position = UDim2.new(0.5, 8, 0, 0)
	getKey.BackgroundColor3 = Color3.new(1, 1, 1)
	getKey.BackgroundTransparency = 0.955
	getKey.Text = "Get Key"
	getKey.TextColor3 = Color3.new(1, 1, 1)
	getKey.Font = Enum.Font.GothamBold
	getKey.TextSize = 14
	getKey.AutoButtonColor = false
	getKey.Parent = btnRow
	Utils.Round(getKey, 14)
	Utils.Stroke(getKey, Color3.new(1, 1, 1), 1, 0.94)
	local function ApplyHover(btn)
		local baseColor = btn.BackgroundColor3
		btn.MouseEnter:Connect(
			function()
				Utils.Tween(
					btn,
					{
						BackgroundColor3 = baseColor:Lerp(Color3.new(1, 1, 1), 0.1)
					},
					0.2
				)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset + 4, btn.Size.Y.Scale, btn.Size.Y.Offset + 2)
					},
					0.2
				)
			end
		)
		btn.MouseLeave:Connect(
			function()
				Utils.Tween(btn, {BackgroundColor3 = baseColor}, 0.2)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset - 4, btn.Size.Y.Scale, btn.Size.Y.Offset - 2)
					},
					0.2
				)
			end
		)
	end
	ApplyHover(redeem)
	ApplyHover(getKey)
	box.Focused:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.5, Thickness = 1.2}, 0.3)
		end
	)
	box.FocusLost:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.95, Thickness = 1}, 0.3)
		end
	)
	local spinConnection
	local dotsThread
	local function SetStatus(state)
		if spinConnection then
			spinConnection:Disconnect()
			spinConnection = nil
			sImg.Rotation = 0
		end
		if dotsThread then
			task.cancel(dotsThread)
			dotsThread = nil
		end
		local color = Configuration.Colors.StatusIdle
		local icon = Icons.Lock
		local text = "No key detected"
		if state == "verifying" then
			color = Configuration.Colors.StatusVerifying
			icon = Icons.Loading
			text = "Verifying access"
			spinConnection =
				RunService.Heartbeat:Connect(
				function(dt)
					if not sImg or not sImg.Parent then
						if spinConnection then
							spinConnection:Disconnect()
						end
						spinConnection = nil
						return
					end
					sImg.Rotation = (sImg.Rotation + dt * 360) % 360
				end
			)
			local dots = {".", "..", "...", ""}
			local i = 1
			dotsThread =
				task.spawn(
				function()
					while sValue and sValue.Parent do
						if not sValue.Text:find("Verifying access", 1, true) then
							break
						end
						sValue.Text = text .. dots[i]
						i = (i % #dots) + 1
						task.wait(0.45)
					end
				end
			)
		elseif state == "success" then
			color = Configuration.Colors.StatusSuccess
			icon = Icons.CheckCircle
			text = "Access Granted"
		elseif state == "error" then
			color = Configuration.Colors.StatusError
			icon = Icons.XCircle
			text = "Invalid Key"
		end
		Utils.Tween(sValue, {TextColor3 = color}, 0.35)
		Utils.Tween(sImg, {ImageColor3 = color}, 0.35)
		Utils.Tween(sIconBg, {BackgroundColor3 = color}, 0.35)
		sValue.Text = text
		sImg.Image = icon
	end
	redeem.MouseButton1Click:Connect(
		function()
			local key = box.Text:upper()
			SetStatus("verifying")
			redeem.Text = "..."
			redeem.Active = false
            local result = Junkie.check_key(key)
			redeem.Active = true
			redeem.Text = "Redeem"
			if not result then
				SetStatus("error")
				ToastSystem.Create(screen, "API request failed: " .. tostring(result), "error")
				return
			end
			if result.valid then
                saveVerifiedKey(key)
                getgenv().SCRIPT_KEY = key
                SetStatus("success")
                ToastSystem.Create(screen, "Access granted!", "success", nil, status)
                task.wait(0.8)
                SetBlur(false)
                Utils.Tween(
                    main,
                    {
                        Position = UDim2.new(0.5, 0, 0.5, 100),
                        BackgroundTransparency = 1
                    },
                    0.7,
                    Enum.EasingStyle.Exponential,
                    Enum.EasingDirection.In
                )
                task.delay(
                    0.7,
                    function()
                        screen:Destroy()
                    end
                )
			else
				SetStatus("error")
				ToastSystem.Create(screen, result.message or "Invalid key", "error", nil, status)
			end
		end
	)
	getKey.MouseButton1Click:Connect(
		function()
			setclipboard(Junkie.get_key_link())
			ToastSystem.Create(screen, "Key link has been copied to clipboard", "success")
		end
	)
	paste.MouseButton1Click:Connect(
		function()
			ToastSystem.Create(screen, "Paste functionality not supported in Roblox (security reasons)", "warning")
		end
	)
	main.Position = UDim2.new(0.5, 0, 0.5, 100)
	main.BackgroundTransparency = 1
	Utils.Tween(
		main,
		{
			Position = UDim2.new(0.5, 0, 0.5, 0),
			BackgroundTransparency = 0.2
		},
		1,
		Enum.EasingStyle.Exponential
	)
	local dragging, dragStart, startPos
	bar.InputBegan:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = true
				dragStart = input.Position
				startPos = main.Position
			end
		end
	)
	UserInputService.InputChanged:Connect(
		function(input)
			if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then
				local delta = input.Position - dragStart
				main.Position =
					UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
			end
		end
	)
	UserInputService.InputEnded:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = false
			end
		end
	)
	return screen
end

local savedKey = loadVerifiedKey()
local keyToCheck = savedKey
if not keyToCheck then
    keyToCheck = getgenv().SCRIPT_KEY
end

local result = Junkie.check_key(keyToCheck)
if result and result.valid then
    if result.message == "KEYLESS" then
        getgenv().SCRIPT_KEY = "KEYLESS"
    elseif result.message == "KEY_VALID" then
        if not savedKey and keyToCheck then
            saveVerifiedKey(keyToCheck)
        end
        getgenv().SCRIPT_KEY = keyToCheck
    else
        Build()
    end
else
    Build()
end

while not getgenv().SCRIPT_KEY do
    task.wait(0.1)
end
end
__y2k_keygate()
-- ===== Protected payload =====
-- Protected with Vm runtime. Tampering halts execution.
-- Vm protection runtime (bundled). Do not edit by hand.
local Crypt = (function()
--!nonstrict
-- ============================================================================
--  Crypt.lua  --  lightweight obfuscation / integrity primitives
--  Part of the Vm protection runtime. No external deps. Luau-safe.
--
--  Provides: XOR string cipher, FNV-1a hash, base64, and a small PRNG so the
--  runtime can hide embedded strings (URLs, function names) and verify
--  integrity without leaving plaintext secrets in the bytecode.
-- ============================================================================

local Crypt = {}

local schar, sbyte, ssub, srep = string.char, string.byte, string.sub, string.rep
local tconcat = table.concat
local bxor = bit32 and bit32.bxor or function(a, b)
	local r, p = 0, 1
	while a > 0 or b > 0 do
		local x, y = a % 2, b % 2
		if x ~= y then r = r + p end
		a, b, p = (a - x) / 2, (b - y) / 2, p * 2
	end
	return r
end

-- 32-bit multiply mod 2^32 that stays within double precision (2^53).
-- Splitting the accumulator into hi/lo 16-bit halves keeps every intermediate
-- product under 2^42, so no precision is lost (a plain h*16777619 overflows 2^53).
local function mul32(a, b)
	local ah = (a - a % 65536) / 65536   -- floor(a / 2^16), < 2^16
	local al = a % 65536                  -- a mod 2^16, < 2^16
	return ((ah * b % 65536) * 65536 + al * b) % 4294967296
end

-- FNV-1a 32-bit hash of a string (used for integrity fingerprints)
function Crypt.hash(s)
	local h = 2166136261
	for i = 1, #s do
		h = bxor(h, sbyte(s, i))
		h = mul32(h, 16777619)
	end
	return h
end

-- repeating-key XOR cipher (symmetric). key is a string.
function Crypt.xor(data, key)
	local out, kl = {}, #key
	for i = 1, #data do
		out[i] = schar(bxor(sbyte(data, i), sbyte(key, (i - 1) % kl + 1)))
	end
	return tconcat(out)
end

-- deterministic PRNG (xorshift) seeded from a string; for shuffling/jitter
function Crypt.rng(seed)
	local state = (type(seed) == "string") and Crypt.hash(seed) or (seed or 0x1234567)
	if state == 0 then state = 0x9E3779B9 end
	return function()
		state = bxor(state, (state * 32) % 4294967296)
		state = bxor(state, math.floor(state / 8))
		state = bxor(state, (state * 16384) % 4294967296)
		state = state % 4294967296
		return state / 4294967296
	end
end

-- base64 (so ciphertext survives as a string literal in the bundle)
local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
function Crypt.b64encode(data)
	local out = {}
	for i = 1, #data, 3 do
		local a, b, c = sbyte(data, i), sbyte(data, i + 1), sbyte(data, i + 2)
		local n = a * 65536 + (b or 0) * 256 + (c or 0)
		local c1 = math.floor(n / 262144) % 64
		local c2 = math.floor(n / 4096) % 64
		local c3 = math.floor(n / 64) % 64
		local c4 = n % 64
		out[#out + 1] = ssub(B64, c1 + 1, c1 + 1)
		out[#out + 1] = ssub(B64, c2 + 1, c2 + 1)
		out[#out + 1] = b and ssub(B64, c3 + 1, c3 + 1) or "="
		out[#out + 1] = c and ssub(B64, c4 + 1, c4 + 1) or "="
	end
	return tconcat(out)
end

local B64I
function Crypt.b64decode(data)
	if not B64I then
		B64I = {}
		for i = 1, #B64 do B64I[ssub(B64, i, i)] = i - 1 end
	end
	data = string.gsub(data, "[^" .. B64 .. "]", "")
	local out = {}
	for i = 1, #data, 4 do
		local a = B64I[ssub(data, i, i)] or 0
		local b = B64I[ssub(data, i + 1, i + 1)] or 0
		local c = B64I[ssub(data, i + 2, i + 2)]
		local d = B64I[ssub(data, i + 3, i + 3)]
		local n = a * 262144 + b * 4096 + (c or 0) * 64 + (d or 0)
		out[#out + 1] = schar(math.floor(n / 65536) % 256)
		if c then out[#out + 1] = schar(math.floor(n / 256) % 256) end
		if d then out[#out + 1] = schar(n % 256) end
	end
	return tconcat(out)
end

-- convenience: encrypt a plaintext to a portable token (b64(xor(data,key)))
function Crypt.seal(plaintext, key)
	return Crypt.b64encode(Crypt.xor(plaintext, key))
end
function Crypt.open(token, key)
	return Crypt.xor(Crypt.b64decode(token), key)
end

return Crypt

end)()
local Secure = (function()
--!nonstrict
-- ============================================================================
--  Secure.lua  --  capture real executor functions & expose protected proxies
--
--  THE CORE PROTECTION. At load time (before any spy can install hooks) we grab
--  references to the real executor functions into PRIVATE upvalues, then hand
--  the wrapped script only thin proxies. Because the proxies call the captured
--  originals directly, a spy that later hooks the GLOBAL `request` / `http` /
--  `readfile` never sees the script's calls -- they bypass the global.
--
--  Proxies are wrapped with newcclosure so they read as native C-closures:
--  iscclosure() passes, and getupvalues() is blocked on them by most executors,
--  hiding the captured originals from getgc/upvalue inspection.
-- ============================================================================

local Secure = {}

-- resolve the real global table as early as possible
local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local rawget, rawset = rawget, rawset
local iscc = iscclosure
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction or function(f) return f end

-- list of sensitive globals we proxy. (function-valued globals only)
local CAPTURE = {
	"request", "http_request", "readfile", "writefile", "appendfile", "isfile",
	"isfolder", "listfiles", "makefolder", "delfile", "delfolder", "loadstring",
	"getgenv", "getrawmetatable", "setrawmetatable", "hookfunction", "hookmetamethod",
	"newcclosure", "getnamecallmethod", "setclipboard", "queue_on_teleport",
	"getcustomasset", "fireclickdetector", "firetouchinterest", "fireproximityprompt",
	"isexecutorclosure", "checkcaller", "getconnections", "getcallingscript",
}

-- Capture the real functions. Returns a PRIVATE table (kept as an upvalue by the
-- caller -- never store this in a global).
function Secure.capture()
	local raw = {}

	-- http via the common executor spellings, in priority order
	raw.http = (syn and syn.request) or (http and http.request) or http_request or request
	-- guard: if http appears already hooked (became an l-closure), remember it
	raw.http_tampered = (iscc and raw.http and not iscc(raw.http)) or false

	for _, name in ipairs(CAPTURE) do
		local fn = rawget(realG, name)
		if type(fn) == "function" then
			-- clone where supported so even a later identity-swap of the global
			-- can't reach our reference
			local ok, c = pcall(clonef, fn)
			raw[name] = ok and c or fn
			raw[name .. "_genuine"] = (iscc and iscc(fn)) or false
		end
	end

	-- HttpGet/HttpGetAsync live on `game`; capture bound callers
	local okGame = pcall(function() return game and game.HttpGet end)
	if okGame and game then
		raw.HttpGet = function(url, ...) return game:HttpGet(url, ...) end
		raw.HttpGetAsync = function(url, ...) return game:HttpGetAsync(url, ...) end
	end

	return raw
end

-- Build the proxy table the sandbox exposes. `raw` is the private capture.
-- Each proxy is a newcclosure so its upvalues (the real fn) are not inspectable.
function Secure.proxies(raw)
	local P = {}

	local function wrap(realFn)
		if type(realFn) ~= "function" then return nil end
		return newcc(function(...) return realFn(...) end)
	end

	-- generic passthrough proxies
	for _, name in ipairs(CAPTURE) do
		if raw[name] then P[name] = wrap(raw[name]) end
	end

	-- unified HTTP proxy (the prime spy target). Accepts the standard {Url=...}.
	if raw.http then
		local http = raw.http
		P.request = newcc(function(opts) return http(opts) end)
		P.http_request = P.request
		if syn then P.syn = { request = P.request } end
	end
	if raw.HttpGet then
		P.HttpGet = newcc(function(url, ...) return raw.HttpGet(url, ...) end)
		P.HttpGetAsync = newcc(function(url, ...) return raw.HttpGetAsync(url, ...) end)
	end

	return P
end

-- Snapshot identities so Integrity can detect later replacement of our proxies.
function Secure.fingerprint(P)
	local fp = {}
	for k, v in pairs(P) do
		if type(v) == "function" then fp[k] = v end
	end
	return fp
end

return Secure

end)()
local Environment = (function()
--!nonstrict
-- ============================================================================
--  Environment.lua  --  the sealed sandbox the wrapped script runs inside
--
--  Builds a custom _ENV whose:
--    * function-valued executor globals resolve to PROTECTED PROXIES
--    * everything else falls through to the real globals (so game, workspace,
--      Instance, math, string, task, etc. all work -- full Luau semantics)
--    * writes stay local to the sandbox (script can't pollute real _G)
--    * the metatable is private (Integrity verifies it wasn't swapped)
--
--  This is the isolation layer: the script believes it has a normal global
--  environment, but its sensitive calls are routed through the Vm.
-- ============================================================================

local Environment = {}

function Environment.build(proxies, realG)
	realG = realG or (getgenv and getgenv()) or _G

	-- the sandbox's own storage for globals the script defines
	local store = {}

	-- private metatable (kept out of the sandbox; Integrity holds a ref)
	local mt = {}

	mt.__index = function(_, key)
		-- 1. protected proxy?
		local p = proxies[key]
		if p ~= nil then return p end
		-- 2. script-local global?
		local s = store[key]
		if s ~= nil then return s end
		-- 3. fall through to the real environment
		return realG[key]
	end

	mt.__newindex = function(_, key, value)
		-- keep all writes inside the sandbox (never touch real globals)
		store[key] = value
	end

	-- unique private lock token. __metatable makes getmetatable(env) return THIS
	-- (hiding the real mt) and makes setmetatable(env, ...) error -- so the env's
	-- metatable cannot be swapped. Integrity verifies this token is still in place.
	local lock = {}
	mt.__metatable = lock

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store, lock
end

return Environment

end)()
local Integrity = (function()
--!nonstrict
-- ============================================================================
--  Integrity.lua  --  anti-tamper / anti-penetration
--
--  Verifies the runtime hasn't been hooked or swapped, both at startup and via
--  a background watchdog. On tamper it triggers a caller-supplied onTamper
--  (the Vm wipes the sandbox + halts).
--
--  Checks:
--   * capture genuineness   -- were the executor funcs already hooked at capture?
--   * proxy identity         -- have our proxies been replaced since fingerprint?
--   * env seal               -- is the sandbox __index/__newindex intact?
--   * hostile introspection  -- is something actively decompiling/hooking us?
--   * source checksum        -- does the protected payload still match?
-- ============================================================================

local Integrity = {}

local iscc = iscclosure
local getus = getupvalues or (debug and debug.getupvalues)

-- 1. Were any captured executor functions already hooks (l-closures) at capture?
function Integrity.checkCapture(raw)
	local suspicious = {}
	if raw.http_tampered then suspicious[#suspicious + 1] = "http" end
	for k, v in pairs(raw) do
		if string.sub(k, -8) == "_genuine" and v == false then
			suspicious[#suspicious + 1] = string.sub(k, 1, -9)
		end
	end
	return suspicious
end

-- 2. Our proxies must still be the exact functions we created.
function Integrity.checkProxies(P, fingerprint)
	for k, original in pairs(fingerprint) do
		if P[k] ~= original then return false, k end
	end
	return true
end

-- 3. The sandbox env metatable must be intact (not re-pointed to leak globals).
function Integrity.checkEnv(env, expectedMT)
	local mt = getmetatable(env)
	if mt ~= expectedMT then return false, "metatable" end
	return true
end

-- 4. Best-effort: detect if our own proxies have become inspectable (a sign a
--    de-hook tool unwrapped the cclosure). On a healthy executor getupvalues on
--    a newcclosure should be empty/blocked; non-empty => someone unwrapped it.
function Integrity.checkOpaque(P)
	if not getus then return true end
	for _, v in pairs(P) do
		if type(v) == "function" then
			local ok, ups = pcall(getus, v)
			if ok and type(ups) == "table" and next(ups) ~= nil then
				return false
			end
		end
	end
	return true
end

-- run all startup checks; returns ok, reason
function Integrity.startup(ctx)
	local sus = Integrity.checkCapture(ctx.raw)
	if #sus > 0 and ctx.strict then
		return false, "capture-hooked:" .. table.concat(sus, ",")
	end
	local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
	if not okP then return false, "proxy-swapped:" .. tostring(badKey) end
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envLock)
	if not okE then return false, "env-" .. tostring(why) end
	if not Integrity.checkOpaque(ctx.proxies) then return false, "opaque-broken" end
	return true
end

-- background watchdog: re-run cheap checks on an interval and self-destruct.
-- Spawns through the Memory scope (ctx.mem) so the thread is tracked and
-- cancelled on cleanup -- it can never leak past the script's lifetime.
function Integrity.watchdog(ctx, onTamper)
	local wait_ = (task and task.wait) or wait
	local body = function()
		while ctx.alive do
			wait_(ctx.interval or 2)
			if not ctx.alive then return end
			local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
			local okE = Integrity.checkEnv(ctx.env, ctx.envLock)
			if not okP or not okE then
				ctx.alive = false
				pcall(onTamper, okP and "env" or ("proxy:" .. tostring(badKey)))
				return
			end
		end
	end
	if ctx.mem and ctx.mem.spawn then
		ctx.mem:spawn(body)
	else
		local spawn = (task and task.spawn) or spawn
		if spawn then spawn(body) end
	end
end

return Integrity

end)()
local Stealth = (function()
--!nonstrict
-- ============================================================================
--  Stealth.lua  --  comprehensive environment spoofing / anti-detection
--
--  Covers the full sUNC executor surface (docs.sunc.su). For each function an
--  anti-cheat could use to fingerprint the executor, detect hooks, or scan for
--  injected objects, we install a fake that answers "clean" -- while leaving the
--  function usable for everyone else.
--
--  Technique: hookfunction (rewrites the function OBJECT, so even a reference
--  the AC captured early is affected), replacement wrapped in newcclosure (stays
--  a C-closure -> passes iscclosure). Everything pcall-guarded; only spoofs what
--  the executor actually exposes.
--
--  HONEST: beats ACs that read these globals at runtime and trust them. Does NOT
--  beat an AC that ran fully before you, re-implements checks in its own VM, or
--  validates server-side. Raises the bar across games.
-- ============================================================================

local Stealth = {}

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction
local hookf = hookfunction
local cloneref_ = cloneref or function(x) return x end
local rawget, rawset = rawget, rawset

-- private registries (weak so we never pin objects alive)
local hiddenObjs = setmetatable({}, { __mode = "k" })  -- hide from gc/instance scans
local genuineFns = setmetatable({}, { __mode = "k" })  -- report as un-hooked / ours
local ourScripts = setmetatable({}, { __mode = "k" })  -- hide script bytecode/closure
local installed  = false

function Stealth.hide(o)        if o ~= nil then hiddenObjs[o] = true end return o end
function Stealth.markGenuine(f) if type(f) == "function" then genuineFns[f] = true end return f end
function Stealth.hideScript(s)  if s ~= nil then ourScripts[s] = true end return s end

-- ---- hook helpers ---------------------------------------------------------
-- CRITICAL: after hookfunction(real, repl), the `real` OBJECT behaves like repl.
-- So the replacement must NOT call `real` on its passthrough path (that would be
-- infinite recursion -> C stack overflow). We clone the original FIRST and have
-- the replacement call the unhooked clone. If we can't clone, we fall back to a
-- plain global swap (which leaves `real` itself untouched, so calling it is safe).
local function emplace(container, name, build)
	if type(container) ~= "table" then return end
	local real = rawget(container, name)
	if type(real) ~= "function" then return end
	if hookf and clonef then
		local okc, orig = pcall(clonef, real)
		if okc and type(orig) == "function" then
			local repl = newcc(build(orig))         -- repl -> clone (unhooked): safe
			genuineFns[repl] = true; hiddenObjs[repl] = true
			if pcall(hookf, real, repl) then return end
		end
	end
	-- fallback: global/table swap, repl -> real (real is NOT hooked here): safe
	local repl = newcc(build(real))
	genuineFns[repl] = true; hiddenObjs[repl] = true
	pcall(rawset, container, name, repl)
end

local function spoof(name, build)            emplace(realG, name, build) end
local function spoofIn(tbl, name, build)     emplace(tbl, name, build) end

-- filter our hidden/genuine objects out of an array-like result table.
local function filterArray(t)
	if type(t) ~= "table" then return t end
	local out = {}
	for i = 1, #t do
		local v = t[i]
		if not (hiddenObjs[v] or genuineFns[v]) then out[#out + 1] = v end
	end
	return out
end

-- ===========================================================================
function Stealth.install(opts)
	if installed then return end
	installed = true
	opts = opts or {}
	local fakeName = opts.spoofName            -- nil => "no executor"
	local fakeVer  = opts.spoofVersion or "1.0.0"

	-- DISGUISE: a real game LocalScript (cloneref'd) to report as the "calling
	-- script", so introspection sees a legit script instead of getcallingscript()
	-- == nil (which screams "injected"). On by default; opts.disguise=false to skip.
	local decoyScript = nil
	if opts.disguise ~= false then
		pcall(function()
			local lp = game:GetService("Players").LocalPlayer
			local char = lp and lp.Character
			decoyScript = (char and char:FindFirstChild("Animate"))
				or (lp and lp:FindFirstChildWhichIsA("LocalScript", true))
		end)
		if decoyScript then pcall(function() decoyScript = cloneref_(decoyScript) end) end
	end

	-- 1) IDENTITY ----------------------------------------------------------
	for _, n in ipairs({ "identifyexecutor", "getexecutorname", "iexecutor" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end

	-- 2) CLOSURE CHECKS ----------------------------------------------------
	spoof("iscclosure",       function(r) return function(f) if genuineFns[f] then return true  end return r(f) end end)
	spoof("isexecutorclosure",function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("isourclosure",     function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("islclosure",       function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("checkcaller",      function(r) return function() return false end end)
	-- stable fake hash for our funcs so repeated checks stay consistent
	spoof("getfunctionhash",  function(r) return function(f) if genuineFns[f] then return "00000000000000000000000000000000" end return r(f) end end)

	-- 3) ENVIRONMENT / GC scans -- strip our objects ----------------------
	spoof("getgc",     function(r) return function(...) return filterArray(r(...)) end end)
	spoof("filtergc",  function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	spoof("getreg",    function(r) return function(...) return filterArray(r(...)) end end)
	-- getgenv/getrenv must keep identity (callers rely on it); objects already hidden via getgc

	-- 4) INSTANCE scans -- strip our injected instances -------------------
	spoof("getinstances",    function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getnilinstances", function(r) return function(...) return filterArray(r(...)) end end)

	-- 5) SCRIPT scans -- hide our scripts/closures ------------------------
	spoof("getloadedmodules", function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getrunningscripts",function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getscripts",       function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getcallingscript", function(r) return function(...) local s = r(...); if ourScripts[s] or s == nil then return decoyScript end return s end end)
	spoof("getscriptbytecode",function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscriptclosure", function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscripthash",    function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	spoof("getsenv",          function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- 6) DEBUG introspection -- blank out for OUR functions ---------------
	if debug then
		spoofIn(debug, "getupvalue",  function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getupvalues", function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getconstant", function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getconstants",function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getproto",    function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getprotos",   function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
	end
	-- top-level mirrors (some executors expose these globally too)
	for _, n in ipairs({ "getupvalue","getupvalues","getconstant","getconstants","getproto","getprotos" }) do
		spoof(n, function(r) return function(f, ...)
			if genuineFns[f] then
				if string.sub(n, -1) == "s" then return {} end
				return nil
			end
			return r(f, ...)
		end end)
	end

	-- 7) common executor extras (Volt/Synapse/etc. spellings that may exist) ----
	for _, n in ipairs({ "getexecutorname", "getexecutor", "getexecutorinfo" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end
	-- decompiler-style probes: refuse on our scripts
	for _, n in ipairs({ "decompile", "disassemble", "dumpstring" }) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	end

	-- 7b) Potassium / extended closure + thread + hook checks --------------
	-- the big one: isfunctionhooked must say NO for the funcs your cheat hooks
	spoof("isfunctionhooked", function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isnewcclosure",    function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isourclosure",     function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	-- "is this the executor / a hook thread" -> no
	spoof("isourthread",      function(r) return function() return false end end)
	-- thread/script linkage: don't reveal our scripts
	spoof("getscriptfromthread", function(r) return function(t, ...) local s = r(t, ...) if ourScripts[s] then return nil end return s end end)
	spoof("getscriptthread",     function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("gettenv",             function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- Potassium oth.* (original-thread hooking) table
	local oth = rawget(realG, "oth")
	if type(oth) == "table" then
		spoofIn(oth, "is_hook_thread", function(r) return function() return false end end)
	end

	-- debug.* extras present on Potassium
	if debug then
		spoofIn(debug, "getcallstack", function(r) return function(...) return r(...) end end)  -- seam: frames aren't our objects
		-- getregistry: return a filtered COPY with our objects removed (AC scans are read-only)
		spoofIn(debug, "getregistry", function(r) return function(...)
			local reg = r(...)
			if type(reg) ~= "table" then return reg end
			local out = {}
			for k, v in pairs(reg) do
				if not (hiddenObjs[k] or hiddenObjs[v] or genuineFns[k] or genuineFns[v]) then
					out[k] = v
				end
			end
			return out
		end end)
		spoofIn(debug, "getinfo", function(r) return function(...) return r(...) end end)  -- seam
	end

	-- metatable seams: only safe to touch CONDITIONALLY. We do NOT blanket-fake
	-- getrawmetatable/getnamecallmethod -- faking the real game metatable breaks
	-- everything. If YOUR cheat hooks __namecall, register the clean function via
	-- Stealth.markGenuine(yourHook) and add a targeted getrawmetatable spoof.

	-- 8) USER-SUPPLIED EXTENSIONS (add Volt-specific names without editing code) -
	--    opts.identity   = { "voltname", ... }     -> spoofed like identifyexecutor
	--    opts.gcFilters  = { "somelist", ... }     -> array results have our objs removed
	--    opts.genuine    = { "iscustom", ... }     -> return clean for our funcs
	--    opts.scriptHide = { "getbytecode2", ... } -> return nothing for our scripts
	for _, n in ipairs(opts.identity or {}) do
		spoof(n, function() return function() if fakeName then return fakeName, fakeVer end return nil end end)
	end
	for _, n in ipairs(opts.gcFilters or {}) do
		spoof(n, function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	end
	for _, n in ipairs(opts.genuine or {}) do
		spoof(n, function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	end
	for _, n in ipairs(opts.scriptHide or {}) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	end

	return true
end

return Stealth

end)()
local Memory = (function()
--!nonstrict
-- ============================================================================
--  Memory.lua  --  resource scope + leak/overflow protection
--
--  Every thread, connection and disposable the VM creates is registered in a
--  scope. When the script ends (return, error, or tamper) the scope is torn down
--  deterministically: threads cancelled, connections disconnected, tables
--  cleared, GC forced. Plus a budget guard that collects GC the moment memory
--  crosses a threshold, so a runaway/hostile script can't balloon the VM.
--
--  Design notes:
--   * Registries that hold game objects use WEAK keys so they never pin memory.
--   * The scope holds STRONG refs to threads/connections (so it can cancel them)
--     but cleanup is GUARANTEED to run, bounding their lifetime.
--   * Counters are capped; nothing grows unbounded.
-- ============================================================================

local Memory = {}
Memory.__index = Memory

local taskLib   = task
local taskSpawn = (taskLib and taskLib.spawn) or spawn
local taskWait  = (taskLib and taskLib.wait) or wait
local taskDefer = (taskLib and taskLib.defer) or taskSpawn
local taskCancel = taskLib and taskLib.cancel
local cg = collectgarbage

local MAX_TRACKED = 4096   -- hard cap so the bookkeeping itself can't leak

function Memory.new()
	return setmetatable({
		alive = true,
		threads = {},
		conns = {},
		disposers = {},
		count = 0,
	}, Memory)
end

local function bounded(self)
	return self.count < MAX_TRACKED
end

-- spawn a tracked thread (auto-cancelled on cleanup)
function Memory:spawn(fn)
	if not self.alive or not bounded(self) then return end
	local co = taskSpawn(fn)
	self.threads[#self.threads + 1] = co
	self.count = self.count + 1
	return co
end

-- track an arbitrary resource with a disposer
function Memory:track(obj, dispose)
	if not self.alive or not bounded(self) then return obj end
	if dispose then
		self.disposers[#self.disposers + 1] = dispose
		self.count = self.count + 1
	end
	return obj
end

-- track a signal connection (auto-disconnected on cleanup)
function Memory:connect(signal, fn)
	if not self.alive or not bounded(self) then return end
	local ok, c = pcall(function() return signal:Connect(fn) end)
	if ok and c then
		self.conns[#self.conns + 1] = c
		self.count = self.count + 1
		return c
	end
end

-- deterministic teardown -- safe to call multiple times
function Memory:cleanup()
	if not self.alive then return end
	self.alive = false
	for _, c in ipairs(self.conns) do
		pcall(function() if c.Disconnect then c:Disconnect() elseif c.disconnect then c:disconnect() end end)
	end
	if taskCancel then
		for _, co in ipairs(self.threads) do pcall(taskCancel, co) end
	end
	for _, d in ipairs(self.disposers) do pcall(d) end
	self.conns, self.threads, self.disposers, self.count = {}, {}, {}, 0
	if cg then pcall(cg, "collect") end
end

-- memory-budget guard: force GC when usage crosses the threshold; if it stays
-- over after a collect, escalate to onOverflow (the Vm halts).
function Memory:guard(opts)
	opts = opts or {}
	local budgetKB = opts.budgetKB or 700000   -- ~700 MB ceiling by default
	local interval = opts.interval or 4
	self:spawn(function()
		while self.alive do
			taskWait(interval)
			if not self.alive then return end
			local used = cg and cg("count") or 0     -- KB
			if used > budgetKB then
				if cg then pcall(cg, "collect") end
				used = cg and cg("count") or 0
				if used > budgetKB and opts.onOverflow then
					pcall(opts.onOverflow, used)
					return
				end
			end
		end
	end)
end

return Memory

end)()
local Defense = (function()
--!nonstrict
-- ============================================================================
--  Defense.lua  --  detect tools SPYING on your script (anti-tamper)
--
--  These detect OTHER exploiters' inspection tools so your script can react
--  (halt / hide) before its logic or remotes are stolen:
--    * HTTP spy      -- request/http hooked (closure-type check vs captured original)
--    * namecall hook -- __namecall identity changed (IY-style stack inspection)
--    * remote spy    -- gcinfo spike on FireServer (spies deep-clone args)  [opt-in]
--    * Dex explorer  -- weak-table service-cache persistence                [opt-in]
--
--  IMPORTANT: this is ANTI-SPY (protect your code from other exploiters), NOT
--  anti-cheat. It does nothing against the GAME's AC -- and the remote/dex probes
--  even ADD client AC surface (they fire a remote / force GC). Keep those opt-in.
-- ============================================================================

local Defense = {}

local gcinfo_   = gcinfo or function() return (collectgarbage and collectgarbage("count")) or 0 end
local cloneref_ = cloneref or function(x) return x end
local collect   = collectgarbage
local iscc      = iscclosure       -- captured at load; Stealth passes through for non-ours
local dbinfo    = debug and debug.info

-- 1) HTTP spy: a spy hooks the global request -> it becomes an l-closure -------
-- get the real __namecall fn via an errored game:IsA() ----------------------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end

local function remoteSpike()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	return (ok and type(spike) == "number") and spike or 0
end

-- BASELINE: snapshot the environment AFTER your script has set up its own hooks,
-- so YOUR hooks are treated as "normal". Only CHANGES after this (a spy) trigger.
-- Until baseline() is called, the change-detectors stay silent (no false positives).
Defense._snap = nil
function Defense.baseline()
	local realG = (getgenv and getgenv()) or _G
	Defense._snap = {
		ready = true,
		nc = (actualNamecall()),
		request = rawget(realG, "request"),
		http_request = rawget(realG, "http_request"),
		getgc = rawget(realG, "getgc"),     -- a dumper re-hooking getgc -> identity change
		spike = remoteSpike(),
	}
	return true
end

-- getgc-scan: someone re-hooked getgc (a memory scanner/dumper) after baseline
function Defense.detectGetgcHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	local cur = rawget(realG, "getgc")
	if cur and s.getgc and cur ~= s.getgc then return true, "getgc re-hooked (memory scan)" end
	return false
end

-- spy-tool GLOBALS (Hydroxide/SimpleSpy/etc. set flags or tables in getgenv)
local SPY_GLOBALS = { "Hydroxide", "oh_load", "SimpleSpy", "SimpleSpyExecuted", "RemoteSpyV3", "IY_LOADED" }
function Defense.detectSpyGlobals()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		for _, n in ipairs(SPY_GLOBALS) do
			if rawget(g, n) ~= nil then return true, "global " .. n end
		end
	end
	return false
end

-- 1) HTTP spy: the request function IDENTITY changed since baseline (newly hooked)
function Defense.detectHttpSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if cur and s[n] and cur ~= s[n] then return true, n .. " changed after baseline" end
	end
	return false
end

-- 2) namecall hook: __namecall identity changed since baseline
function Defense.detectNamecallHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local nc = actualNamecall()
	if s.nc and nc and nc ~= s.nc then return true, "__namecall changed after baseline" end
	return false
end

-- 3) remote spy: gc spike on FireServer rose ABOVE the baseline (a new arg-cloner)
function Defense.detectRemoteSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local spike = remoteSpike()
	if spike > (s.spike or 0) + 64 then
		return true, "FireServer gc spike " .. tostring(spike)
	end
	return false
end

-- 4a) Infinite Yield (and similar admin tools) set a known global flag --------
function Defense.detectInfiniteYield()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		if rawget(g, "IY_LOADED") == true then return true, "Infinite Yield" end
	end
	return false
end

-- 4b) Spy/explorer GUIs (Dex, RemoteSpy, SimpleSpy, Hydroxide, IY window) ------
-- scans CoreGui, the executor-hidden gui (gethui), and PlayerGui by exact name.
-- PRECISE name matching: exact known names, plus controlled version patterns,
-- so we don't false-positive on legit GUIs (e.g. "Dexterity" must NOT match "dex").
local EXACT = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true, ["remote spy"] = true,
	["simplespy"] = true, ["simple spy"] = true, ["hydroxide"] = true,
}
local function isSpyName(nm)
	if EXACT[nm] then return true end
	if string.match(nm, "^dex%s*v?%d") then return true end          -- "dex v4", "dex 5"
	if string.match(nm, "^remotespy") then return true end
	if string.match(nm, "^simplespy") then return true end
	if string.match(nm, "^hydroxide") then return true end
	return false
end
function Defense.detectSpyGui()
	local parents = {}
	pcall(function() parents[#parents + 1] = game:GetService("CoreGui") end)
	if gethui then pcall(function() parents[#parents + 1] = gethui() end) end
	pcall(function()
		local pg = game:GetService("Players").LocalPlayer:FindFirstChild("PlayerGui")
		if pg then parents[#parents + 1] = pg end
	end)
	for _, p in ipairs(parents) do
		local ok, kids = pcall(function() return p:GetChildren() end)
		if ok then
			for _, c in ipairs(kids) do
				if isSpyName(string.lower(c.Name)) then return true, "GUI: " .. c.Name end
			end
		end
	end
	return false
end

-- 4) Dex: it strong-caches services, so a weak ref survives a forced GC -------
function Defense.detectDex()
	local ok, persisted = pcall(function()
		local weak = setmetatable({}, { __mode = "v" })
		weak[1] = cloneref_(game:GetService("TestService"))
		weak[1] = weak[1]   -- (kept only in the weak table after this scope)
		if collect then for _ = 1, 3 do pcall(collect, "collect") end end
		return weak[1] ~= nil
	end)
	return ok and persisted == true
end

-- SaveInstance guard: hook saveinstance-family so a game/script DUMP is caught
-- the moment it's attempted. Call once (from the watchdog) with the reaction.
function Defense.installSaveGuard(onDetect)
	local realG = (getgenv and getgenv()) or _G
	local newcc_ = newcclosure or function(f) return f end
	local hookf, clonef = hookfunction, clonefunction
	for _, n in ipairs({ "saveinstance", "synsaveinstance", "SaveInstance", "saveplace" }) do
		local f = rawget(realG, n)
		if type(f) == "function" and hookf and clonef then
			local ok, orig = pcall(clonef, f)
			if ok then
				pcall(hookf, f, newcc_(function(...)
					pcall(onDetect, "saveinstance", n)
					return orig(...)
				end))
			end
		end
	end
end

-- run a scan; returns array of { name = , detail = }
function Defense.scan(opts)
	opts = opts or {}
	local found = {}
	local function run(enabled, fn, name, arg)
		if not enabled then return end
		local ok, detail = fn(arg)
		if ok then found[#found + 1] = { name = name, detail = detail or "" } end
	end
	run(opts.iy ~= false,        Defense.detectInfiniteYield, "infinite-yield")
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- Dex/RemoteSpy/IY window
	run(opts.globals ~= false,   Defense.detectSpyGlobals,    "spy-global")  -- Hydroxide/SimpleSpy/etc.
	run(opts.http ~= false,      Defense.detectHttpSpy,       "http-spy")
	run(opts.namecall ~= false,  Defense.detectNamecallHook,  "namecall-hook")
	run(opts.getgc ~= false,     Defense.detectGetgcHook,     "getgc-scan")  -- dumper re-hooked getgc
	run(opts.remote == true,     Defense.detectRemoteSpy,     "remote-spy")  -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,           "dex")         -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	-- proactive SaveInstance dump guard (fires the moment a dump is attempted)
	pcall(Defense.installSaveGuard, onDetect)
	local body = function()
		local wait_ = (task and task.wait) or wait
		wait_(opts.startDelay or 1)            -- let tools finish loading
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
		-- baseline after a grace period so the script's OWN hooks aren't flagged
		-- (Vm also baselines right after the main chunk; whichever fires first wins).
		local graceUntil = (tick and tick() or 0) + (opts.gracePeriod or 4)
		while ctx.alive do
			n = n + 1
			if not (Defense._snap and Defense._snap.ready) and (tick and tick() or 0) >= graceUntil then
				pcall(Defense.baseline)
			end
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui, globals = opts.globals,
				http = opts.http, namecall = opts.namecall, getgc = opts.getgc,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				local h = hits[1]
				local need = NOISY[h.name] and 2 or 1        -- reliable = instant, noisy = confirm twice
				if h.name == lastHit then confirm = confirm + 1
				else lastHit, confirm = h.name, 1 end
				if confirm >= need then
					pcall(onDetect, h.name, h.detail)
					return
				end
			else
				lastHit, confirm = nil, 0
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

end)()
local Neuter = (function()
--!nonstrict
-- ============================================================================
--  Neuter.lua  --  best-effort anti-cheat neutralizer (with honest reporting)
--
--  Attempts, in order, every CLIENT-SIDE technique to blind an AC, and REPORTS
--  the outcome of each. If it can't bypass, it says so loudly:
--      "AC bypass fail (error; <reason>)"
--  rather than silently pretending you're undetected.
--
--  Strategies:
--    1. global-spoof   -- replace detection globals with clean-answering versions
--    2. upvalue-patch  -- find ACs that captured detection fns as upvalues and
--                         debug.setupvalue them to our clean versions
--    3. table-patch    -- replace detection fns held in (writable) state tables
--                         (reaches some VM-style ACs)
--    4. report-block   -- best-effort: neutralize the global HTTP request path
--
--  HARD TRUTH (always reported): this is CLIENT-SIDE only. An AC that is
--  VM-obfuscated (functions buried in encrypted state -> nothing to patch) or
--  that validates SERVER-SIDE cannot be bypassed from here. Rivals is both.
-- ============================================================================

local Neuter = {}

local newcc   = newcclosure or function(f) return f end
local getgc_  = getgc
local getups  = getupvalues or (debug and debug.getupvalues)
local setup   = debug and debug.setupvalue
local realG   = (getgenv and getgenv()) or _G
local rawget, rawset = rawget, rawset

local SCAN_CAP = 300000

-- clean-answering replacements: AC sees "no executor, nothing hooked"
local function replacements()
	local R = {}
	R.identifyexecutor   = newcc(function() return nil end)
	R.getexecutorname    = newcc(function() return nil end)
	R.getexecutor        = newcc(function() return nil end)
	R.iscclosure         = newcc(function() return true end)   -- everything looks native
	R.isexecutorclosure  = newcc(function() return false end)
	R.isourclosure       = newcc(function() return false end)
	R.islclosure         = newcc(function() return false end)
	R.isfunctionhooked   = newcc(function() return false end)
	R.checkcaller        = newcc(function() return false end)
	R.isourthread        = newcc(function() return false end)
	return R
end

-- map ORIGINAL function identity -> replacement (for patching captured refs)
local function identityMap(R)
	local m = {}
	for name, repl in pairs(R) do
		local orig = rawget(realG, name)
		if type(orig) == "function" then m[orig] = repl end
	end
	return m
end

-- 1) global spoof -----------------------------------------------------------
function Neuter.globalSpoof(R)
	local n = 0
	for name, repl in pairs(R) do
		if type(rawget(realG, name)) == "function" then
			if hookfunction and clonefunction then
				local ok, orig = pcall(clonefunction, rawget(realG, name))
				if ok then pcall(hookfunction, rawget(realG, name), repl) else pcall(rawset, realG, name, repl) end
			else
				pcall(rawset, realG, name, repl)
			end
			n = n + 1
		end
	end
	return n > 0, "spoofed " .. n .. " globals", 0
end

-- 2) upvalue patch ----------------------------------------------------------
function Neuter.patchUpvalues(idmap)
	if not (getgc_ and getups and setup) then return false, "no getgc/debug.setupvalue" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, fn in ipairs(getgc_(false) or getgc_()) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(fn) == "function" then
				local oku, ups = pcall(getups, fn)
				if oku and type(ups) == "table" then
					for i, uv in pairs(ups) do
						if idmap[uv] then
							if pcall(setup, fn, i, idmap[uv]) then patched = patched + 1 end
						end
					end
				end
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " captured upvalue(s) of " .. scanned .. " closures", patched
end

-- 3) table patch (reaches some VM-style ACs that read fns from state tables) -
function Neuter.patchTables(idmap)
	if not getgc_ then return false, "no getgc" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, t in ipairs(getgc_(true)) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(t) == "table" then
				pcall(function()
					for k, v in pairs(t) do
						if idmap[v] then
							if pcall(function() t[k] = idmap[v] end) then patched = patched + 1 end
						end
					end
				end)
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " table slot(s)", patched
end

-- 4) report block (best-effort) --------------------------------------------
function Neuter.blockReporting()
	-- We can only neutralize a report path we can see. The global request is
	-- proxied by Secure already; an AC-internal report channel inside a VM is
	-- not generically locatable, so report this honestly.
	return false, "report channel not generically locatable (AC-internal)"
end

-- orchestrate ---------------------------------------------------------------
function Neuter.run(opts)
	opts = opts or {}
	local logf = opts.log or function(m) pcall(warn, m) end
	local R = replacements()
	local idmap = identityMap(R)

	local results, patched = {}, 0
	local function strat(name, fn, ...)
		local ok, detail, n = fn(...)
		results[#results + 1] = { name = name, ok = ok, detail = detail }
		if type(n) == "number" then patched = patched + n end
		logf("[Neuter] " .. name .. ": " .. (ok and "OK" or "FAIL") .. " -- " .. tostring(detail))
	end

	strat("global-spoof",  Neuter.globalSpoof, R)
	strat("upvalue-patch", Neuter.patchUpvalues, idmap)
	strat("table-patch",   Neuter.patchTables, idmap)
	strat("report-block",  Neuter.blockReporting)

	-- VERDICT (honest)
	local verdict
	if patched > 0 then
		verdict = "client checks neutralized (" .. patched .. " refs patched). "
			.. "WARNING: server-side validation is NOT affected -- this is not full immunity."
		logf("[Neuter] result: PARTIAL -- " .. verdict)
	else
		verdict = "no patchable detection refs found -- AC is VM-obfuscated/absent or "
			.. "captures privately; nothing to neutralize client-side."
		logf("AC bypass fail (error; " .. verdict .. ")")
	end

	return { patched = patched, results = results, ok = patched > 0, verdict = verdict }
end

return Neuter

end)()
local License = (function()
--!nonstrict
-- ============================================================================
--  License.lua  --  key / HWID whitelist, expiry, server validation, delivery
--
--  Anti-leak core. A protected script can require a valid KEY (+ optional HWID
--  lock) before it runs, enforce an EXPIRY, and/or fetch its real payload from
--  YOUR server only after the key checks out (so a leaked file is useless).
--
--  Validation order (any you configure):
--    1. expiry      -- refuse if past opts.expiry (server time when possible)
--    2. local keys  -- opts.keys = { "KEY1", ... } embedded allow-list
--    3. server      -- GET opts.endpoint?key=..&hwid=..  -> body must contain "ok"
--  If none configured, it allows (no license).
-- ============================================================================

local License = {}

local function httpGet(url)
	local fns = {
		function() return game:HttpGetAsync(url) end,
		function() return game:HttpGet(url) end,
		function() return request and request({ Url = url, Method = "GET" }).Body end,
	}
	for _, f in ipairs(fns) do
		local ok, body = pcall(f)
		if ok and type(body) == "string" then return body end
	end
	return nil
end

-- stable per-machine id
function License.hwid()
	local id
	pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
	if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
	return tostring(id or "unknown")
end

-- tamper-resistant time: try a web time source, fall back to os.time
function License.now()
	local body = httpGet("https://worldtimeapi.org/api/timezone/Etc/UTC.txt")
	if body then
		local ut = string.match(body, "unixtime:%s*(%d+)")
		if ut then return tonumber(ut) end
	end
	return os.time and os.time() or 0
end

local function inList(list, key)
	for _, k in ipairs(list) do if k == key then return true end end
	return false
end

-- returns ok, reason
function License.validate(opts)
	opts = opts or {}

	if opts.expiry then
		local now = License.now()
		if now and now > 0 and now > opts.expiry then
			return false, "license expired"
		end
	end

	if opts.endpoint then
		local hwid = License.hwid()
		local sep = string.find(opts.endpoint, "?", 1, true) and "&" or "?"
		local url = opts.endpoint .. sep .. "key=" .. tostring(opts.key or "")
			.. "&hwid=" .. hwid
		local body = httpGet(url)
		if not body then return false, "license server unreachable" end
		local lb = string.lower(body)
		if string.find(lb, "ok", 1, true) or string.find(lb, "valid", 1, true) then
			return true, "ok", body  -- body may carry the payload for server-delivery
		end
		return false, "key rejected by server"
	end

	if opts.keys then
		if opts.key and inList(opts.keys, opts.key) then return true, "ok" end
		return false, "invalid key"
	end

	return true, "no license configured"
end

-- SERVER-SIDE DELIVERY: validate, and if the server returns the (encrypted)
-- payload in its response, return it so the loader can run it. Body format the
-- reference server uses:  "ok\n<base64-xored-payload>"  (key is the xor key).
function License.deliver(opts)
	local ok, reason, body = License.validate(opts)
	if not ok then return nil, reason end
	if body then
		local nl = string.find(body, "\n", 1, true)
		if nl then return string.sub(body, nl + 1), "ok" end
	end
	return nil, "validated (no payload in response)"
end

return License

end)()
local Vm = (function()
--!nonstrict
-- ============================================================================
--  Vm.lua  --  main entry of the Vm protection runtime
--
--  Orchestrates Secure (capture+proxies), Environment (sandbox), and Integrity
--  (anti-tamper), then runs the wrapped script inside the sealed runtime.
--
--  API:
--    Vm.run(chunk [, opts])     -- chunk = source string OR a function
--    Vm.protect(fn [, opts])    -- returns a hardened wrapper of fn
--
--  opts = {
--    name     = "Sell a Lemon",      -- label for errors/telemetry
--    strict   = false,                -- abort if executor funcs look pre-hooked
--    interval = 2,                    -- watchdog period (seconds)
--    onTamper = function(reason) end, -- override default self-destruct
--    checksum = "<fnv hash>",         -- optional source integrity pin
--  }
-- ============================================================================

local Crypt       = Crypt
local Secure      = Secure
local Environment = Environment
local Integrity   = Integrity
local Stealth     = Stealth
local Memory      = Memory
local Defense     = Defense
local Neuter      = Neuter
local License     = License

local Vm = {}
Vm._VERSION = "1.0.0"

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local loadstr = loadstring or load
local setfenv_ = setfenv

-- default self-destruct: wipe the sandbox + raise, so a tampered run cannot
-- continue executing the protected logic.
local function defaultTamper(ctx, reason)
	ctx.alive = false
	-- neuter the proxies so any in-flight call resolves to nothing
	for k in pairs(ctx.proxies) do ctx.proxies[k] = nil end
	if ctx.mem then pcall(function() ctx.mem:cleanup() end) end  -- free threads/conns
	error("[Vm] integrity violation (" .. tostring(reason) .. ") -- halted", 0)
end

-- Build a fresh, sealed runtime context.
local function newContext(opts)
	-- install anti-detection FIRST (as early as we can), then hide our own
	-- objects from gc/closure scans so the spoofing can't be traced back to us.
	if opts.stealth ~= false then
		pcall(Stealth.install, opts.stealthOpts or {})
	end

	-- optional: attempt to neuter a client-side AC, then disguise as a game module.
	-- Reports "AC bypass fail (error; ...)" if it can't (VM-obfuscated / server-side).
	if opts.neuterAC then
		pcall(Neuter.run, type(opts.neuterAC) == "table" and opts.neuterAC or {})
	end

	local raw = Secure.capture()
	local proxies = Secure.proxies(raw)
	local fingerprint = Secure.fingerprint(proxies)
	local env, envMT, _store, envLock = Environment.build(proxies, realG)

	-- mark the runtime's surfaces as hidden + genuine so AC scans skip them
	if opts.stealth ~= false then
		Stealth.hide(raw); Stealth.hide(proxies); Stealth.hide(env)
		for _, fn in pairs(proxies) do
			if type(fn) == "function" then Stealth.markGenuine(fn) end
		end
	end

	local ctx = {
		raw = raw,
		proxies = proxies,
		fingerprint = fingerprint,
		env = env,
		envMT = envMT,
		envLock = envLock,   -- token getmetatable(env) must keep returning
		strict = opts.strict or false,
		interval = opts.interval or 2,
		alive = true,
		name = opts.name or "script",
		mem = Memory.new(),   -- resource scope: tracks every thread/connection
	}

	-- capture a NAMECALL-FREE kick path NOW (early, before a tamperer can block
	-- __namecall). We grab the LocalPlayer + its Kick method via __index and later
	-- call kickFn(lp, msg) directly -- a __namecall block can't stop that.
	pcall(function()
		local plrs = game:GetService("Players")
		ctx.lp = plrs.LocalPlayer
		ctx.kickFn = ctx.lp and ctx.lp.Kick
	end)

	return ctx
end

-- Core: run a function inside a sealed context with integrity enforced.
function Vm.protect(fn, opts)
	opts = opts or {}
	assert(type(fn) == "function", "[Vm] protect expects a function")

	return function(...)
		local ctx = newContext(opts)

		-- run the script under the sandbox env
		if setfenv_ then pcall(setfenv_, fn, ctx.env) end

		local onTamper = function(reason)
			if opts.onTamper then pcall(opts.onTamper, reason) end
			defaultTamper(ctx, reason)
		end

		-- startup integrity gate
		local ok, reason = Integrity.startup(ctx)
		if not ok then return onTamper(reason) end

		-- background watchdog (tracked by the memory scope)
		Integrity.watchdog(ctx, onTamper)

		-- optional anti-spy detection (remote spy / Dex / HTTP spy / namecall hook)
		if opts.antiSpy then
			local o = type(opts.antiSpy) == "table" and opts.antiSpy or {}
			Defense.watchdog(ctx, function(name, detail)
				if opts.onSpy then pcall(opts.onSpy, name, detail) end
				-- clean message (no details). Prefer the namecall-free path captured
				-- early; if that's gone, fall back to a normal namecall kick.
				if o.kick ~= false then
					local kicked = false
					if ctx.kickFn and ctx.lp then
						kicked = pcall(ctx.kickFn, ctx.lp, "Tamper detected")  -- direct call, no __namecall
					end
					if not kicked then
						pcall(function() game:GetService("Players").LocalPlayer:Kick("Tamper detected") end)
					end
				end
				-- crash the tamperer's client -- the guaranteed fallback if the kick is
				-- blocked. IMPORTANT: NOT wrapped in pcall (a pcall would swallow the
				-- out-of-memory error and stop the crash). Allocations are kept alive in
				-- `sink` so GC can't reclaim them; big chunks per iteration -> OOM in ~1s.
				-- Runs in its own thread so cleanup can't cancel it.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local wait_ = (task and task.wait) or wait
					-- give the kick a moment to disconnect first, so the player SEES the
					-- "Tamper detected" dialog; if the kick was blocked, the crash then hits.
					pcall(function() wait_(o.crashDelay or 1.5) end)
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(16777216, 0)   -- ~256MB/iter
							else
								sink[#sink + 1] = string.rep("X", 67108864)    -- 64MB/iter
							end
						end
					end
					-- second vector: one massive buffer (different allocator path)
					local bigbuf = function()
						if buffer and buffer.create then local _ = buffer.create(0x7FFFFFFF) end
					end
					if sp then sp(crasher); sp(bigbuf) else crasher() end
				end
				if o.halt ~= false then
					ctx.alive = false
					pcall(function() ctx.mem:cleanup() end)
				end
			end, o)
		end

		-- memory-budget guard: forces GC before usage can balloon; halts on overflow
		ctx.mem:guard({
			budgetKB = opts.memBudgetKB,
			interval = opts.interval,
			onOverflow = function(used)
				ctx.alive = false
				if opts.onOverflow then pcall(opts.onOverflow, used) end
				pcall(function() ctx.mem:cleanup() end)
			end,
		})

		-- execute the script's main chunk
		local results = { pcall(fn, ...) }

		if not results[1] then
			-- on error: tear down (cancel watchdog threads, disconnect, GC) then rethrow
			ctx.alive = false
			pcall(function() ctx.mem:cleanup() end)
			error("[Vm:" .. ctx.name .. "] " .. tostring(results[2]), 0)
		end

		-- SUCCESS: do NOT tear down. Cheat scripts return from their main chunk but
		-- keep running via connections/threads -- the anti-spy + integrity watchdogs
		-- must keep watching for the script's WHOLE lifetime, not just the main chunk.
		-- (Teardown happens on tamper, overflow, or spy-kick.)

		-- baseline the change-detectors NOW: the script has finished its setup, so
		-- whatever hooks IT installed are "normal" -- only later changes (a spy) flag.
		if opts.antiSpy then pcall(Defense.baseline) end

		return table.unpack(results, 2)
	end
end

-- Convenience: load a source string and protect+run it.
function Vm.run(chunk, opts)
	opts = opts or {}

	-- LICENSE gate (key / HWID / expiry / server). Runs before anything executes.
	if opts.license then
		local ok, reason = License.validate(opts.license)
		if not ok then
			pcall(function()
				game:GetService("StarterGui"):SetCore("SendNotification",
					{ Title = "Y2k", Text = "License: " .. tostring(reason), Duration = 6 })
			end)
			error("[Vm] license check failed: " .. tostring(reason), 0)
		end
	end

	-- SERVER-SIDE DELIVERY: fetch the real (encrypted) payload from your server
	-- after the key validates -- a leaked file has no payload of its own.
	if opts.deliver then
		local payload, reason = License.deliver(opts.deliver)
		if not payload then error("[Vm] delivery failed: " .. tostring(reason), 0) end
		chunk = (opts.deliver.key and Crypt.open(payload, opts.deliver.key)) or payload
	end

	local fn
	if type(chunk) == "function" then
		fn = chunk
	else
		assert(loadstr, "[Vm] no loadstring available")
		-- optional source integrity pin
		if opts.checksum and Crypt.hash(chunk) ~= opts.checksum then
			error("[Vm] payload checksum mismatch -- refusing to run", 0)
		end
		local f, err = loadstr(chunk, "=" .. (opts.name or "Vm"))
		if not f then error("[Vm] load error: " .. tostring(err), 0) end
		fn = f
	end
	return Vm.protect(fn, opts)()
end

return Vm

end)()

local __k = 'ohZG7MmPhlrUjw9D18Gpygnd'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-7UinV3ch0EDf
return Vm.run(__src, { name = 'Keyboard escape/keyboard escape', checksum = 1715464684, interval = 2, watermark = 'Y2k-7UinV3ch0EDf', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
